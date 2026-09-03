use arbitrary::{Arbitrary, Unstructured};
use diesel_fuzz::jsonb::ArbitraryJsonb;
use diesel_fuzz::jsonb::{
    Header, Leniency, agree, check_decode, check_encode, check_encode_bytes, check_strictness,
    encode_header, explains_divergence, has_known_panic, has_known_reader_defect, json_eq,
    known_writer_defect, rendered_eq, repair, walk,
};
use diesel_fuzz::sqlite::{
    decode_jsonb, encode_jsonb, jsonb_strictly_valid, text_to_jsonb, with_conn,
};

#[test]
fn walk_flattens_an_object() {
    let tags: Vec<u8> = with_conn(|conn| {
        let blob = text_to_jsonb(conn, r#"{"a":[1,null]}"#).unwrap();
        walk(&blob).iter().map(|element| element.tag).collect()
    });
    assert_eq!(
        tags,
        vec![
            diesel_fuzz::jsonb::OBJECT,
            diesel_fuzz::jsonb::TEXT,
            diesel_fuzz::jsonb::ARRAY,
            diesel_fuzz::jsonb::INT,
            diesel_fuzz::jsonb::NULL,
        ]
    );
}

#[test]
fn walk_stops_at_an_impossible_size() {
    assert!(walk(&[0xC7, 0xFF, b'a']).is_empty());
}

/// Each class, on the blob whose divergence it explains.
#[test]
fn divergence_classes() {
    with_conn(|conn| {
        for (blob, class) in [
            ([0x10, 0x00].as_slice(), Leniency::ConstantPayload),
            (&[0x11, 0x08], Leniency::ConstantPayload),
            (&[0x17, 0x0D], Leniency::TextEscaping),
            (&[0x17, b'"'], Leniency::TextEscaping),
            (&[0x23, b'4', b' '], Leniency::NumericFormat),
            (&[0x24, b'0', b'x'], Leniency::Json5Type),
            (b"\xc3\x14-9223372806354775808", Leniency::NumberOutOfRange),
            (&[0x17, 0x9C], Leniency::NonUtf8Text),
        ] {
            assert_eq!(
                explains_divergence(conn, blob),
                Some(vec![class]),
                "{blob:02X?}"
            );
        }
    });
}

/// A blob diesel and sqlite agree on carries nothing to explain.
#[test]
fn an_agreed_blob_has_no_class() {
    with_conn(|conn| {
        assert_eq!(explains_divergence(conn, &[0x17, b'a']), None);
        assert_eq!(explains_divergence(conn, &[0x35, b'1', b'.', b'5']), None);
    });
}

/// A payload sqlite accepts whose syntax diesel refuses is a format class, not
/// a range one: the name has to identify the cause.
#[test]
fn syntax_and_range_are_separate_classes() {
    with_conn(|conn| {
        for (payload, class) in [
            (b"01".as_slice(), Leniency::NumericFormat),
            (b"1 ", Leniency::NumericFormat),
            (b"+1", Leniency::NumericFormat),
            (b"9223372036854775808", Leniency::NumberOutOfRange),
        ] {
            let blob = leaf(diesel_fuzz::jsonb::INT, payload);
            assert_eq!(
                explains_divergence(conn, &blob),
                Some(vec![class]),
                "{:?}",
                str::from_utf8(payload)
            );
        }
    });
}

#[test]
fn sqlite_written_blobs_agree() {
    let docs = [
        "null",
        "true",
        "-9223372036854775808",
        "1.5e300",
        "\"\"",
        "\"\\u0000\\u001f\\\"\\\\\"",
        "\"\\ud83d\\ude00\"",
        "[]",
        "{}",
        "[null,true,1,\"a\",[],{}]",
        "{\"a\":{\"b\":[1,2,{\"c\":null}]},\"d\":\"\\t\"}",
        "[[[[[[[[[[1]]]]]]]]]]",
        "{\"dup\":1,\"dup\":2}",
    ];
    with_conn(|conn| {
        for doc in docs {
            let blob = text_to_jsonb(conn, doc).unwrap();
            assert!(check_decode(conn, &blob).is_none(), "{doc}");
            assert!(check_strictness(conn, &blob).is_none(), "{doc}");
        }
    });
}

#[test]
fn known_leniency_is_not_reported() {
    with_conn(|conn| {
        for blob in [
            [0x10, 0x00].as_slice(),
            &[0x11, 0x08],
            &[0x17, 0x0D],
            &[0x23, b'4', b' '],
        ] {
            assert!(check_decode(conn, blob).is_none(), "{blob:02X?}");
        }
    });
}

#[test]
fn values_round_trip_through_the_writer() {
    with_conn(|conn| {
        for text in [
            "null",
            "true",
            "-1",
            "0.5",
            "\"a\"",
            "[1,2]",
            "{\"a\":null}",
        ] {
            let value: serde_json::Value = serde_json::from_str(text).unwrap();
            assert!(check_encode(conn, &value).is_none(), "{text}");
        }
    });
}

/// Witness; delete with the fix.
#[test]
fn float_writer_emits_unreadable_blobs() {
    with_conn(|conn| {
        for text in ["3.0", "-0.0", "1.5e300"] {
            let value: serde_json::Value = serde_json::from_str(text).unwrap();
            let blob = encode_jsonb(conn, &value).expect("a blob");
            assert!(!jsonb_strictly_valid(conn, &blob), "{text}");
            // skipped by shape, so every other value stays under test
            assert!(check_encode(conn, &value).is_none(), "{text}");
        }
    });
}

/// Witness; delete with the fix.
#[test]
fn string_writer_emits_unreadable_blobs() {
    with_conn(|conn| {
        for text in ["\"a\":1", "back\\slash", "quote\"inside"] {
            let value = serde_json::Value::String(text.to_string());
            let blob = encode_jsonb(conn, &value).expect("a blob");
            assert!(!jsonb_strictly_valid(conn, &blob), "{text}");
            assert!(check_encode(conn, &value).is_none(), "{text}");
        }
    });
}

#[test]
fn the_blob_generator_produces_decodable_input() {
    let seed: Vec<u8> = (0u8..=255).collect();
    let ArbitraryJsonb(blob) = ArbitraryJsonb::arbitrary(&mut Unstructured::new(&seed)).unwrap();
    assert!(!blob.is_empty());
    with_conn(|conn| {
        assert!(check_decode(conn, &blob).is_none(), "{blob:02X?}");
    });
}

/// The grammar must reach an INT payload past `i64::MAX`, which the classifier
/// calls `NumberOutOfRange` and byte mutation rarely spells inside a container.
#[test]
fn the_blob_generator_reaches_unsigned_int_payloads() {
    let unsigned = (0u8..=255).any(|byte| {
        let seed: Vec<u8> = (0u8..=255).map(|b| b.wrapping_add(byte)).collect();
        let ArbitraryJsonb(blob) =
            ArbitraryJsonb::arbitrary(&mut Unstructured::new(&seed)).expect("a blob");
        walk(&blob).iter().any(|element| {
            element.tag == diesel_fuzz::jsonb::INT
                && str::from_utf8(element.payload).is_ok_and(|payload| {
                    payload.parse::<i64>().is_err() && payload.parse::<u64>().is_ok()
                })
        })
    });
    assert!(unsigned, "no seed produced an INT payload above i64::MAX");
}

fn leaf(tag: u8, payload: &[u8]) -> Vec<u8> {
    let mut blob = encode_header(Header::narrowest(payload.len()), tag, payload.len());
    blob.extend(payload);
    blob
}

fn container(tag: u8, children: &[&[u8]]) -> Vec<u8> {
    leaf(tag, &children.concat())
}

/// The panic guard reads headers, not payload bytes, and says nothing about
/// trailing bytes: crash safety is not a semantic question.
#[test]
fn the_panic_guard_only_covers_the_overflowing_header() {
    let overflow = [0xFFu8; 9];
    assert!(has_known_panic(&overflow));

    let mut payload = vec![(0x0Cu8 << 4) | diesel_fuzz::jsonb::TEXT, 9];
    payload.extend(overflow);
    assert!(
        !has_known_panic(&payload),
        "a header shape inside a payload is not a header"
    );

    let mut trailing = leaf(diesel_fuzz::jsonb::INT, b"1");
    trailing.push(0x00);
    assert!(!has_known_panic(&trailing));
    assert!(
        has_known_reader_defect(&trailing),
        "trailing bytes stay a semantic defect"
    );
}

/// A class only explains a divergence if removing it makes the divergence go.
#[test]
fn a_class_must_cause_the_divergence() {
    with_conn(|conn| {
        let quote = leaf(diesel_fuzz::jsonb::TEXT, b"\"");
        let plain = leaf(diesel_fuzz::jsonb::TEXT, b"ab");
        let huge = leaf(diesel_fuzz::jsonb::FLOAT, b"1e999");

        let escaping = container(diesel_fuzz::jsonb::ARRAY, &[&quote, &plain]);
        assert_eq!(
            explains_divergence(conn, &escaping),
            Some(vec![Leniency::TextEscaping])
        );

        let unrepresentable = container(diesel_fuzz::jsonb::ARRAY, &[&plain, &huge]);
        assert_eq!(
            explains_divergence(conn, &unrepresentable),
            Some(vec![Leniency::NumberOutOfRange])
        );

        // an object with a key and no value: no feature of a sibling explains that
        let odd = container(diesel_fuzz::jsonb::OBJECT, &[&plain]);
        let hidden = container(diesel_fuzz::jsonb::ARRAY, &[&odd, &quote]);
        assert_eq!(explains_divergence(conn, &hidden), None);
    });
}

/// Sqlite rendering a number `serde_json` cannot hold is a classified
/// rejection, not a silent skip.
#[test]
fn an_unrepresentable_rendering_is_classified() {
    with_conn(|conn| {
        let blob = text_to_jsonb(conn, "1e999").expect("sqlite encodes it");
        assert!(jsonb_strictly_valid(conn, &blob));
        assert!(decode_jsonb(conn, &blob).is_err());
        assert_eq!(
            explains_divergence(conn, &blob),
            Some(vec![Leniency::NumberOutOfRange])
        );
        assert!(check_strictness(conn, &blob).is_none());
    });
}

/// A text payload that is not utf-8 is classified the same way.
#[test]
fn a_non_utf8_rendering_is_classified() {
    with_conn(|conn| {
        let blob = leaf(diesel_fuzz::jsonb::TEXT, &[0x9C]);
        assert!(jsonb_strictly_valid(conn, &blob));
        assert_eq!(
            explains_divergence(conn, &blob),
            Some(vec![Leniency::NonUtf8Text])
        );
        assert!(check_strictness(conn, &blob).is_none());
    });
}

/// Witness; delete with the fix. The mismatch is classified rather than
/// reported, so the target stays enabled for every other mismatch.
#[test]
fn constants_with_payload_disagree_with_sqlite() {
    with_conn(|conn| {
        for blob in [
            [0x30u8, 0x0D, 0x00, 0xF3].as_slice(),
            &[0x31, 0x31, 0x2E, 0x35],
            &[0x2B, 0xC1, 0x00],
        ] {
            assert!(!agree(conn, blob), "{blob:02X?}");
            assert_eq!(
                explains_divergence(conn, blob),
                Some(vec![Leniency::ConstantPayload]),
                "{blob:02X?}"
            );
            assert!(check_decode(conn, blob).is_none(), "{blob:02X?}");
        }
    });
}

/// The panic guard descends: the overflowing header can sit inside a container
/// whose child cannot be split.
#[test]
fn the_panic_guard_descends_into_containers() {
    let mut blob = vec![(0x0Cu8 << 4) | diesel_fuzz::jsonb::OBJECT, 12];
    blob.extend([0xFFu8; 13]);
    blob.extend([0x75, 0x4C, 0x13, 0x32]);
    assert!(has_known_panic(&blob));
}

/// Every instance of a class is repaired, not just the first: one sibling left
/// in place would report its own class as unexplained.
#[test]
fn a_class_is_repaired_in_every_sibling() {
    with_conn(|conn| {
        let json5 = leaf(diesel_fuzz::jsonb::TEXT5, b"");
        let null = leaf(diesel_fuzz::jsonb::NULL, b"");
        let blob = container(
            diesel_fuzz::jsonb::ARRAY,
            &[&json5, &null, &json5, &null, &null, &null, &null, &null],
        );
        assert!(jsonb_strictly_valid(conn, &blob));
        assert_eq!(
            explains_divergence(conn, &blob),
            Some(vec![Leniency::Json5Type])
        );
        assert!(check_strictness(conn, &blob).is_none());
    });
}

/// Two different classes in one document are both named: repairing either one
/// alone would leave the other's divergence standing.
#[test]
fn every_class_present_is_reported() {
    with_conn(|conn| {
        let quote = leaf(diesel_fuzz::jsonb::TEXT, b"\"");
        let json5 = leaf(diesel_fuzz::jsonb::INT5, b"0x1f");
        let blob = container(diesel_fuzz::jsonb::ARRAY, &[&quote, &json5]);

        assert_eq!(
            explains_divergence(conn, &blob),
            Some(vec![Leniency::TextEscaping, Leniency::Json5Type])
        );

        // neither repair alone restores agreement
        let escaping_only = container(
            diesel_fuzz::jsonb::ARRAY,
            &[&leaf(diesel_fuzz::jsonb::TEXTRAW, b"\""), &json5],
        );
        assert!(!agree(conn, &escaping_only));
        let json5_only = container(
            diesel_fuzz::jsonb::ARRAY,
            &[&quote, &leaf(diesel_fuzz::jsonb::INT, b"1")],
        );
        assert!(!agree(conn, &json5_only));
    });
}

/// Sqlite keeps a lone surrogate escape; a Rust `String` cannot hold one, so
/// the refusal is classified rather than reported.
#[test]
fn a_lone_surrogate_escape_is_classified() {
    with_conn(|conn| {
        let mut blob = vec![(0x0Cu8 << 4) | diesel_fuzz::jsonb::TEXTJ, 12];
        blob.extend(b"\\ud83dTude00");
        assert!(jsonb_strictly_valid(conn, &blob));
        assert!(decode_jsonb(conn, &blob).is_err());
        assert_eq!(
            explains_divergence(conn, &blob),
            Some(vec![Leniency::EscapeNotRepresentable])
        );
        assert!(check_strictness(conn, &blob).is_none());
    });
}

#[test]
fn integers_past_the_f64_mantissa_are_not_equal() {
    let left = serde_json::json!(9_007_199_254_740_992i64);
    let right = serde_json::json!(9_007_199_254_740_993i64);
    assert!(!json_eq(&left, &right));
}

#[test]
fn a_negative_integer_past_the_mantissa_is_not_equal_to_its_neighbour() {
    let left = serde_json::json!(-9_007_199_254_740_992i64);
    let right = serde_json::json!(-9_007_199_254_740_993i64);
    assert!(!json_eq(&left, &right));
}

#[test]
fn a_large_unsigned_integer_is_not_equal_to_its_neighbour() {
    let left = serde_json::json!(18_446_744_073_709_551_615u64);
    let right = serde_json::json!(18_446_744_073_709_551_614u64);
    assert!(!json_eq(&left, &right));
}

#[test]
fn an_integer_equals_the_same_integer_typed_unsigned() {
    let left = serde_json::json!(9_007_199_254_740_993i64);
    let right = serde_json::json!(9_007_199_254_740_993u64);
    assert!(json_eq(&left, &right));
}

#[test]
fn a_float_still_compares_through_f64() {
    let left = serde_json::json!(1.0f64);
    let right = serde_json::json!(1i64);
    assert!(json_eq(&left, &right));
}

/// A repair rewrites the feature and nothing else: an untouched sibling keeps
/// even a wider header than its payload needs, so a novel bug that depends on
/// one cannot vanish into the reconstruction.
#[test]
fn a_repair_keeps_every_untouched_byte() {
    let wide = vec![(0x0Cu8 << 4) | diesel_fuzz::jsonb::TEXT, 1, b'a'];
    let quote = leaf(diesel_fuzz::jsonb::TEXT, b"\"");
    let blob = container(diesel_fuzz::jsonb::ARRAY, &[&wide, &quote]);

    let (repaired, classes) = repair(&blob).expect("a known feature");
    assert_eq!(classes, vec![Leniency::TextEscaping]);

    let mut expected = blob.clone();
    let tag = blob.len() - 2;
    expected[tag] = (0x01 << 4) | diesel_fuzz::jsonb::TEXTRAW;
    assert_eq!(repaired, expected);
}

/// Every size class boundary, since a header that claims a size it cannot
/// write would panic on the way out.
#[test]
fn header_classes_cover_their_boundaries() {
    for (size, class) in [
        (0x0B, Header::Inline),
        (0x0C, Header::Byte),
        (usize::from(u8::MAX), Header::Byte),
        (usize::from(u8::MAX) + 1, Header::Word),
        (usize::from(u16::MAX), Header::Word),
        (usize::from(u16::MAX) + 1, Header::Long),
    ] {
        assert_eq!(Header::narrowest(size), class, "{size}");
        assert!(size <= class.capacity(), "{size}");
    }

    // a 32 bit usize cannot hold this size at all, so there is nothing to check
    if let Ok(over_long) = usize::try_from(u64::from(u32::MAX) + 1) {
        assert_eq!(Header::narrowest(over_long), Header::Quad);
        assert!(over_long > Header::Long.capacity());
        let header = encode_header(Header::Long, diesel_fuzz::jsonb::TEXT, over_long);
        assert_eq!(header.len(), 9, "the class must widen instead of panicking");
    }
}

/// A class only explains a divergence once the repaired blob reads the same
/// under both, so an unrelated value mismatch cannot hide behind it.
#[test]
fn agreement_is_about_the_value_not_just_acceptance() {
    with_conn(|conn| {
        assert!(agree(conn, &leaf(diesel_fuzz::jsonb::INT, b"1")));
        // sqlite reads 11.5 where diesel reads true: both accept, and disagree
        assert!(!agree(conn, &[0x31, 0x31, 0x2E, 0x35]));
        assert!(!agree(conn, &leaf(diesel_fuzz::jsonb::INT5, b"0x1f")));
    });
}

#[test]
fn a_mixed_pair_beyond_the_exact_float_range_is_not_equal() {
    let integer = serde_json::json!(u64::MAX);
    let float = serde_json::json!(18_446_744_073_709_551_615.0_f64);
    assert!(!json_eq(&integer, &float));
}

#[test]
fn a_mixed_pair_inside_the_exact_float_range_is_equal() {
    let integer = serde_json::json!(9_007_199_254_740_992i64);
    let float = serde_json::json!(9_007_199_254_740_992.0_f64);
    assert!(json_eq(&integer, &float));
}

#[test]
fn a_fractional_float_never_equals_an_integer() {
    assert!(!json_eq(&serde_json::json!(1.5), &serde_json::json!(1)));
}

/// The writer path for a `u64` past `i64::MAX` is reachable from a document.
#[test]
fn a_document_can_carry_an_unsigned_number_above_i64() {
    let value: serde_json::Value =
        serde_json::from_slice(b"18446744073709551615").expect("a document");
    assert!(value.as_u64().is_some() && value.as_i64().is_none());
}

/// Witness; delete with the fix.
#[test]
fn the_writer_rounds_unsigned_numbers_above_i64() {
    with_conn(|conn| {
        let value = serde_json::json!(u64::MAX);
        let blob = diesel_fuzz::sqlite::encode_jsonb(conn, &value).expect("a blob");
        assert_eq!(
            diesel_fuzz::sqlite::decode_jsonb(conn, &blob).expect("a value"),
            serde_json::json!(1.8446744073709552e19_f64)
        );
        assert!(!jsonb_strictly_valid(conn, &blob));
        assert!(check_encode(conn, &value).is_none());
    });
}

/// Witness; delete with the fix. Exactly the reported shapes are skipped, so
/// every other document the writer sees stays under test.
#[test]
fn the_writer_guard_names_only_the_reported_shapes() {
    for value in [
        serde_json::json!(3.0),
        serde_json::json!(-0.0),
        serde_json::json!(1.5e300),
        serde_json::json!(u64::MAX),
        serde_json::json!("quote\"inside"),
        serde_json::json!(["ok", {"key": 2.0}]),
        serde_json::json!({"back\\slash": 1}),
    ] {
        assert!(known_writer_defect(&value), "{value}");
    }
    for value in [
        serde_json::json!(1.5),
        serde_json::json!(-7),
        serde_json::json!(i64::MIN),
        serde_json::json!("\u{1}\t\u{7f}"),
        serde_json::json!([1, [2, {"a": null}]]),
        serde_json::json!({"dup": 1}),
    ] {
        assert!(!known_writer_defect(&value), "{value}");
    }
}

/// A seed reaches the value it spells, not entropy for a generator.
#[test]
fn the_encode_target_parses_its_input() {
    with_conn(|conn| {
        assert!(check_encode_bytes(conn, b"[1,2]").is_none());
        assert!(check_encode_bytes(conn, b"not json").is_none());
    });
}

/// Sqlite renders a double with fifteen significant digits, so its rendering
/// cannot be held to more; diesel against diesel still compares exactly.
#[test]
fn the_oracle_rendering_is_compared_at_its_own_precision() {
    let written = serde_json::json!(-922.372_368_547_758_1_f64);
    let rendered = serde_json::json!(-922.372_368_547_758_f64);
    assert!(rendered_eq(&written, &rendered));
    assert!(!json_eq(&written, &rendered));
    assert!(!rendered_eq(
        &serde_json::json!(1.5),
        &serde_json::json!(1.6)
    ));
}
