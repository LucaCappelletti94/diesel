use arbitrary::Arbitrary;
use diesel_fuzz::{document, mysql, pg, sqlite};
use std::num::NonZeroU32;

#[test]
fn every_pg_case_decodes_without_panicking() {
    let oid = NonZeroU32::MIN;
    for selector in 0..pg::CASES.len() {
        let selector = u8::try_from(selector).expect("under 256 cases");
        for bytes in [&[][..], &[0x00], &[0xFF; 4], &[0x7F; 16], &[0xAA; 64]] {
            pg::decode_case(selector, oid, bytes);
        }
    }
}

#[test]
fn every_mysql_case_decodes_without_panicking() {
    for selector in 0..mysql::CASES.len() {
        let selector = u8::try_from(selector).expect("under 256 cases");
        for tpe in 0..mysql::TYPES.len() {
            let tpe = u8::try_from(tpe).expect("under 256 types");
            for bytes in [&[][..], &[0x00], &[0xFF; 4], &[0x30; 12]] {
                mysql::decode_case(selector, tpe, bytes);
            }
        }
    }
}

#[test]
fn every_sqlite_case_decodes_without_panicking() {
    for selector in 0..sqlite::CASES.len() {
        let selector = u8::try_from(selector).expect("under 256 cases");
        for kind in 0..4 {
            for bytes in [
                &[][..],
                &[0x00],
                &[0xFF; 8],
                b"2024-06-15 10:30:45",
                b"1.5e3",
            ] {
                sqlite::decode_case(selector, kind, bytes);
            }
        }
    }
}

#[test]
fn documents_survive_the_round_trip() {
    sqlite::with_conn(|conn| {
        for document in [
            "null",
            "true",
            "false",
            "0",
            "-1",
            "1.5",
            "1e-7",
            "\"\"",
            "\"a\"",
            "[]",
            "{}",
            "[null,true,1,\"a\",[],{}]",
            "{\"a\":{\"b\":[1,2,3]}}",
        ] {
            let value: serde_json::Value = serde_json::from_str(document).expect("valid json");
            sqlite::roundtrip_jsonb(conn, &value).expect(document);
            sqlite::roundtrip_json(conn, &value).expect(document);
        }
    });
}

#[test]
fn generated_documents_stay_within_the_read_limit() {
    for bytes in [
        vec![0xC5; 976],
        vec![0x06; 976],
        vec![0xFF; 976],
        vec![0x00; 976],
        (0u8..=255).cycle().take(4096).collect(),
    ] {
        let mut unstructured = arbitrary::Unstructured::new(&bytes);
        let document =
            document::Document::arbitrary(&mut unstructured).expect("documents from bytes");
        assert!(
            document.nesting() <= document::MAX_NESTING,
            "the generator exceeded the depth serde_json reads"
        );
    }
}

#[test]
fn a_document_at_the_read_limit_survives_the_round_trip() {
    let mut value = serde_json::Value::Null;
    for _ in 0..document::MAX_NESTING {
        value = serde_json::Value::Array(vec![value]);
    }
    sqlite::with_conn(|conn| {
        sqlite::roundtrip_jsonb(conn, &value).expect("jsonb at the nesting cap");
        sqlite::roundtrip_json(conn, &value).expect("json text at the nesting cap");
    });
}

#[test]
fn a_decoded_blob_is_the_one_sqlite_calls_valid() {
    sqlite::with_conn(|conn| {
        assert_eq!(sqlite::jsonb_valid(conn, &[0x00]), Ok(true));
        assert_eq!(sqlite::jsonb_valid(conn, &[0xFF]), Ok(false));
        assert!(sqlite::decode_jsonb(conn, &[0xFF]).is_err());
    });
}

mod query_builder {
    use chrono::DateTime;
    use diesel_fuzz::query::{
        AggBig, AggBool, AggInt, Arith, ArrayOp, Binary, Bool, Bounds, Comparison, Grouping, Input,
        Int, IntArray, IntColumn, Json, JsonKey, JsonKind, Jsonb, Matcher, Net, NetMask, NetOp,
        Nulls, Order, PgBool, PgInt, PgJson, PgText, Query, Range, RangeCombine, RangeOp,
        RemoveKey, Stamp, StampTz, Subquery, Text, TextColumn, Zoned, pg, sqlite,
    };
    use serde_json::json;
    use std::collections::Bound;

    fn int(tree: Int) -> Box<Int> {
        Box::new(tree)
    }

    fn text(tree: Text) -> Box<Text> {
        Box::new(tree)
    }

    fn boolean(tree: Bool) -> Box<Bool> {
        Box::new(tree)
    }

    fn a() -> Box<Int> {
        int(Int::Column(IntColumn::A))
    }

    fn b() -> Box<Int> {
        int(Int::Column(IntColumn::B))
    }

    fn s() -> Box<Text> {
        text(Text::Column(TextColumn::S))
    }

    fn n() -> Box<Text> {
        text(Text::Column(TextColumn::N))
    }

    /// `a - (b - 3)`, which reads differently once the inner parentheses go.
    fn right_nested() -> Int {
        Int::Arith(
            Arith::Sub,
            a(),
            int(Int::Arith(Arith::Sub, b(), int(Int::Literal(3)))),
        )
    }

    fn subquery() -> Box<Subquery> {
        Box::new(Subquery {
            select: right_nested(),
            filter: Some(Bool::Compare(Comparison::Gt, a(), b())),
        })
    }

    fn keys() -> Vec<JsonKey> {
        vec![
            JsonKey::Name("a".to_owned()),
            JsonKey::Position(1),
            JsonKey::Text(text(Text::Concat(s(), n()))),
            JsonKey::Int(int(right_nested())),
        ]
    }

    /// Places `predicate` under a `NOT` inside a `CASE`, where a lost parenthesis would show.
    fn query(postgres: bool, int_tree: Int, text_tree: Text, predicate: Bool) -> Query {
        Query {
            postgres,
            distinct: false,
            int: Int::Case {
                when: boolean(Bool::Not(boolean(predicate))),
                then: int(int_tree),
                second: Some((
                    boolean(Bool::Or(
                        boolean(Bool::Column),
                        boolean(Bool::And(
                            boolean(Bool::Column),
                            boolean(Bool::Literal(true)),
                        )),
                    )),
                    int(Int::Arith(Arith::Div, a(), b())),
                )),
                otherwise: Some(int(Int::Arith(Arith::Mul, a(), int(Int::Literal(-2))))),
            },
            text: Text::Concat(s(), text(text_tree)),
            bool: Bool::Or(
                boolean(Bool::Column),
                boolean(Bool::And(
                    boolean(Bool::Column),
                    boolean(Bool::Literal(false)),
                )),
            ),
            filter: Some(Bool::Not(boolean(Bool::IsNull {
                negated: false,
                value: int(Int::Arith(Arith::Add, a(), b())),
            }))),
            order: Some(Order {
                key: right_nested(),
                descending: true,
                nulls: postgres.then_some(Nulls::First),
            }),
            limit: None,
            offset: None,
        }
    }

    fn assert_oracles_pass(query: &Query) {
        if let Err(violation) = pg::check(query) {
            panic!("{violation}");
        }
        if let Err(violation) = sqlite::check(query) {
            panic!("{violation}");
        }
    }

    fn shared_predicates() -> Vec<Bool> {
        let mut predicates = vec![
            Bool::Column,
            Bool::Literal(false),
            Bool::CompareText(Comparison::LtEq, s(), n()),
            Bool::IsNullText {
                negated: true,
                value: n(),
            },
            Bool::Exists(subquery()),
        ];
        for op in [
            Comparison::Eq,
            Comparison::NotEq,
            Comparison::Lt,
            Comparison::LtEq,
            Comparison::Gt,
            Comparison::GtEq,
        ] {
            predicates.push(Bool::Compare(op, a(), int(right_nested())));
        }
        for negated in [false, true] {
            predicates.push(Bool::Between {
                negated,
                value: a(),
                low: b(),
                high: int(Int::Literal(5)),
            });
            predicates.push(Bool::In {
                negated,
                value: b(),
                list: vec![0, 2],
            });
            predicates.push(Bool::In {
                negated,
                value: b(),
                list: Vec::new(),
            });
            predicates.push(Bool::InSubquery {
                negated,
                value: b(),
                subquery: subquery(),
            });
            predicates.push(Bool::IsNull {
                negated,
                value: b(),
            });
            predicates.push(Bool::Distinct {
                negated,
                left: a(),
                right: b(),
            });
            for matcher in [Matcher::Like, Matcher::ILike, Matcher::SimilarTo] {
                for escape in [None, Some('!'), Some('\0')] {
                    predicates.push(Bool::Match {
                        matcher,
                        negated,
                        value: s(),
                        pattern: text(Text::Concat(n(), text(Text::Literal("%".to_owned())))),
                        escape,
                    });
                }
                // `\%` matches only the literal `%` of `a%b`, so the answer changes without `ESCAPE`
                predicates.push(Bool::Match {
                    matcher,
                    negated,
                    value: s(),
                    pattern: text(Text::Literal("a\\%b".to_owned())),
                    escape: Some('\\'),
                });
            }
        }
        predicates
    }

    fn shared_ints() -> Vec<Int> {
        vec![
            right_nested(),
            Int::FromText(text(Text::Concat(s(), n()))),
            Int::Scalar(subquery()),
        ]
    }

    fn shared_texts() -> Vec<Text> {
        let mut texts = vec![
            Text::FromInt(int(right_nested())),
            Text::FromJson(Box::new(Json::FromText(text(Text::Concat(s(), n()))))),
        ];
        for key in keys() {
            texts.push(Text::JsonField(Box::new(Json::Column), key));
        }
        for key in keys() {
            texts.push(Text::JsonField(
                Box::new(Json::Field(
                    Box::new(Json::Literal(json!({"a": [1, {"b": 2}], "1": "x"}))),
                    key,
                )),
                JsonKey::Position(0),
            ));
        }
        texts
    }

    #[test]
    fn every_shared_node_passes_both_oracles() {
        for predicate in shared_predicates() {
            assert_oracles_pass(&query(
                false,
                right_nested(),
                Text::Literal("x".to_owned()),
                predicate,
            ));
        }
        for int_tree in shared_ints() {
            assert_oracles_pass(&query(
                false,
                int_tree,
                Text::Literal("x".to_owned()),
                Bool::Column,
            ));
        }
        for text_tree in shared_texts() {
            assert_oracles_pass(&query(false, right_nested(), text_tree, Bool::Column));
        }
    }

    fn jsonb() -> Box<Jsonb> {
        Box::new(Jsonb::Concat(
            Box::new(Jsonb::Column),
            Box::new(Jsonb::Literal(json!({"k": [1, 2]}))),
        ))
    }

    fn ints() -> Box<IntArray> {
        Box::new(IntArray::Concat(
            Box::new(IntArray::Column),
            Box::new(IntArray::Literal(vec![1, 2])),
        ))
    }

    fn range() -> Box<Range> {
        Box::new(Range::Combine(
            RangeCombine::Union,
            Box::new(Range::Column),
            Box::new(Range::Literal(Bound::Included(1), Bound::Excluded(9))),
        ))
    }

    fn net() -> Box<Net> {
        Box::new(Net::Mask(
            NetMask::And,
            Box::new(Net::Column),
            Box::new(Net::Literal("10.0.0.0/8".parse().expect("a network"))),
        ))
    }

    fn postgres_arrays() -> Vec<IntArray> {
        let mut arrays = vec![
            IntArray::Build(vec![right_nested()]),
            IntArray::Build(vec![right_nested(), *a()]),
            IntArray::Build(vec![right_nested(), *a(), *b()]),
            IntArray::FromSubquery(subquery()),
        ];
        for bounds in [
            Bounds::Both(a(), int(right_nested())),
            Bounds::From(int(right_nested())),
            Bounds::To(a()),
        ] {
            arrays.push(IntArray::Slice(ints(), bounds));
        }
        for bounds in [Bounds::Both(1, 2), Bounds::From(1), Bounds::To(2)] {
            arrays.push(IntArray::SliceLiteral(ints(), bounds));
        }
        arrays
    }

    fn postgres_jsonbs() -> Vec<Jsonb> {
        let mut values = vec![
            Jsonb::Remove(jsonb(), RemoveKey::Name("k".to_owned())),
            Jsonb::Remove(jsonb(), RemoveKey::Position(0)),
            Jsonb::Remove(
                jsonb(),
                RemoveKey::Names(vec!["k".to_owned(), "j".to_owned()]),
            ),
            Jsonb::RemovePath(jsonb(), vec!["k".to_owned(), "0".to_owned()]),
            Jsonb::Path(jsonb(), vec!["k".to_owned()]),
            Jsonb::FromText(text(Text::Concat(s(), n()))),
            Jsonb::FromJson(Box::new(Json::Column)),
        ];
        for key in keys() {
            values.push(Jsonb::Field(jsonb(), key));
        }
        values
    }

    fn postgres_predicates() -> Vec<Bool> {
        let mut predicates = vec![
            PgBool::FromInt(int(right_nested())),
            PgBool::HasKey(jsonb(), text(Text::Concat(s(), n()))),
            PgBool::HasAnyKey(jsonb(), vec!["k".to_owned()]),
            PgBool::HasAllKeys(jsonb(), vec!["k".to_owned(), "j".to_owned()]),
            PgBool::JsonbContains(jsonb(), jsonb()),
            PgBool::JsonbIsContainedBy(jsonb(), jsonb()),
            PgBool::RangeHas(range(), int(right_nested())),
            PgBool::InRange(int(right_nested()), range()),
            PgBool::NetDistance(Comparison::Gt, net(), net(), 3),
        ];
        for kind in [
            JsonKind::Any,
            JsonKind::Object,
            JsonKind::Array,
            JsonKind::Scalar,
        ] {
            for negated in [false, true] {
                predicates.push(PgBool::IsJson {
                    kind,
                    negated,
                    value: text(Text::Concat(s(), n())),
                });
            }
        }
        for op in [ArrayOp::Overlaps, ArrayOp::Contains, ArrayOp::IsContainedBy] {
            predicates.push(PgBool::Array(op, ints(), ints()));
        }
        for op in [
            RangeOp::Contains,
            RangeOp::IsContainedBy,
            RangeOp::Overlaps,
            RangeOp::ExtendsRightTo,
            RangeOp::ExtendsLeftTo,
            RangeOp::LesserThan,
            RangeOp::GreaterThan,
            RangeOp::Adjacent,
        ] {
            predicates.push(PgBool::Range(op, range(), range()));
        }
        for combine in [
            RangeCombine::Union,
            RangeCombine::Difference,
            RangeCombine::Intersection,
        ] {
            predicates.push(PgBool::Range(
                RangeOp::Overlaps,
                Box::new(Range::Combine(combine, range(), range())),
                range(),
            ));
        }
        for op in [
            NetOp::Contains,
            NetOp::ContainsOrEq,
            NetOp::IsContainedBy,
            NetOp::IsContainedByOrEq,
            NetOp::Overlaps,
        ] {
            predicates.push(PgBool::Net(op, net(), net()));
        }
        predicates.push(PgBool::Net(
            NetOp::Overlaps,
            Box::new(Net::Mask(NetMask::Or, net(), net())),
            Box::new(Net::FromText(n())),
        ));
        let zone = || text(Text::Concat(s(), n()));
        predicates.push(PgBool::Stamp(
            Comparison::Lt,
            Box::new(Stamp::AtZone(
                Box::new(Zoned::StampTz(Box::new(StampTz::Column))),
                zone(),
            )),
            Box::new(Stamp::AtZone(
                Box::new(Zoned::Stamp(Box::new(Stamp::Literal(
                    DateTime::from_timestamp(0, 0)
                        .expect("the epoch")
                        .naive_utc(),
                )))),
                zone(),
            )),
        ));
        predicates.push(PgBool::StampTz(
            Comparison::GtEq,
            Box::new(StampTz::Column),
            Box::new(StampTz::Literal(
                DateTime::from_timestamp(0, 0).expect("the epoch"),
            )),
        ));
        for negated in [false, true] {
            for escape in [None, Some('!')] {
                predicates.push(PgBool::BinaryMatch {
                    negated,
                    value: Box::new(Binary::Concat(
                        Box::new(Binary::Column),
                        Box::new(Binary::Literal(vec![0, 255])),
                    )),
                    pattern: Box::new(Binary::Literal(b"%".to_vec())),
                    escape,
                });
            }
        }
        for array in postgres_arrays() {
            predicates.push(PgBool::Array(ArrayOp::Overlaps, Box::new(array), ints()));
        }
        for value in postgres_jsonbs() {
            predicates.push(PgBool::JsonbContains(Box::new(value), jsonb()));
        }
        predicates.into_iter().map(Bool::Postgres).collect()
    }

    fn postgres_ints() -> Vec<Int> {
        vec![
            Int::Postgres(PgInt::FromBool(boolean(Bool::Column))),
            Int::Postgres(PgInt::Index(ints(), int(right_nested()))),
            Int::Postgres(PgInt::IndexLiteral(
                Box::new(IntArray::Slice(ints(), Bounds::From(a()))),
                1,
            )),
        ]
    }

    fn postgres_texts() -> Vec<Text> {
        let mut texts = vec![
            Text::Postgres(PgText::FromBool(boolean(Bool::Column))),
            Text::Postgres(PgText::FromJsonb(jsonb())),
            Text::Postgres(PgText::FromNet(net())),
            Text::Postgres(PgText::JsonbPath(jsonb(), vec!["k".to_owned()])),
            Text::FromJson(Box::new(Json::Postgres(PgJson::FromJsonb(jsonb())))),
        ];
        for key in keys() {
            texts.push(Text::Postgres(PgText::JsonbField(jsonb(), key)));
        }
        texts
    }

    #[test]
    fn every_postgres_node_passes_the_postgres_oracle() {
        for predicate in postgres_predicates() {
            assert_oracles_pass(&query(
                true,
                right_nested(),
                Text::Literal("x".to_owned()),
                predicate,
            ));
        }
        for int_tree in postgres_ints() {
            assert_oracles_pass(&query(
                true,
                int_tree,
                Text::Literal("x".to_owned()),
                Bool::Column,
            ));
        }
        for text_tree in postgres_texts() {
            assert_oracles_pass(&query(true, right_nested(), text_tree, Bool::Column));
        }
    }

    #[test]
    fn every_clause_passes_both_oracles() {
        for (distinct, limit, offset) in [
            (true, None, None),
            (false, Some(2), None),
            (false, None, Some(1)),
            (false, Some(3), Some(2)),
            (false, Some(0), Some(6)),
        ] {
            for postgres in [false, true] {
                let mut query = query(
                    postgres,
                    Int::Arith(Arith::Add, int(Int::Column(IntColumn::G)), a()),
                    Text::Literal("x".to_owned()),
                    Bool::Compare(Comparison::Gt, int(Int::Column(IntColumn::G)), b()),
                );
                query.distinct = distinct;
                query.limit = limit;
                query.offset = offset;
                assert_oracles_pass(&query);
            }
        }
    }

    fn grouped_ints() -> Vec<AggInt> {
        let min = || Box::new(AggInt::Min(int(right_nested())));
        vec![
            AggInt::Key,
            AggInt::Literal(4),
            AggInt::Max(a()),
            AggInt::Arith(
                Arith::Sub,
                min(),
                Box::new(AggInt::Arith(Arith::Sub, Box::new(AggInt::Key), min())),
            ),
            AggInt::Arith(
                Arith::Mul,
                Box::new(AggInt::Key),
                Box::new(AggInt::Arith(
                    Arith::Add,
                    min(),
                    Box::new(AggInt::Literal(1)),
                )),
            ),
        ]
    }

    fn grouped_bigs() -> Vec<AggBig> {
        vec![
            AggBig::Literal(7),
            AggBig::Sum(int(right_nested())),
            AggBig::Count(b()),
            AggBig::CountStar,
        ]
    }

    fn grouped_predicates() -> Vec<AggBool> {
        let sum = || Box::new(AggBig::Sum(a()));
        vec![
            AggBool::Literal(true),
            AggBool::Compare(
                Comparison::Lt,
                Box::new(AggInt::Key),
                Box::new(AggInt::Max(b())),
            ),
            AggBool::CompareBig(
                Comparison::GtEq,
                Box::new(AggBig::CountStar),
                Box::new(AggBig::Literal(2)),
            ),
            AggBool::IsNull {
                negated: true,
                value: Box::new(AggInt::Min(b())),
            },
            AggBool::Not(Box::new(AggBool::Or(
                Box::new(AggBool::CompareBig(
                    Comparison::Eq,
                    sum(),
                    Box::new(AggBig::Count(a())),
                )),
                Box::new(AggBool::And(
                    Box::new(AggBool::IsNull {
                        negated: false,
                        value: Box::new(AggInt::Key),
                    }),
                    Box::new(AggBool::Literal(false)),
                )),
            ))),
        ]
    }

    fn assert_grouped_oracles_pass(tree: &Grouping) {
        if let Err(violation) = pg::check_grouped(tree) {
            panic!("{violation}");
        }
        if let Err(violation) = sqlite::check_grouped(tree) {
            panic!("{violation}");
        }
    }

    #[test]
    fn every_grouped_node_passes_both_oracles() {
        let filter = || Some(Bool::Compare(Comparison::NotEq, a(), int(Int::Literal(7))));
        for int_tree in grouped_ints() {
            assert_grouped_oracles_pass(&Grouping {
                postgres: false,
                int: int_tree,
                big: AggBig::CountStar,
                filter: filter(),
                having: None,
            });
        }
        for big in grouped_bigs() {
            assert_grouped_oracles_pass(&Grouping {
                postgres: false,
                int: AggInt::Key,
                big,
                filter: None,
                having: None,
            });
        }
        for having in grouped_predicates() {
            assert_grouped_oracles_pass(&Grouping {
                postgres: false,
                int: AggInt::Key,
                big: AggBig::CountStar,
                filter: filter(),
                having: Some(having),
            });
        }
    }

    #[test]
    fn sqlite_queries_draw_no_postgres_node() {
        use arbitrary::{Arbitrary, Unstructured};

        let mut state: u64 = 1;
        let mut bytes = vec![0u8; 2048];
        let mut sqlite_queries = 0;
        for _ in 0..4096 {
            for byte in &mut bytes {
                state = state
                    .wrapping_mul(6_364_136_223_846_793_005)
                    .wrapping_add(1_442_695_040_888_963_407);
                *byte = (state >> 33) as u8;
            }
            let Ok(input) = Input::arbitrary(&mut Unstructured::new(&bytes)) else {
                continue;
            };
            match input {
                Input::Rows(query) if !query.postgres => {
                    sqlite_queries += 1;
                    assert!(query.order.is_none_or(|order| order.nulls.is_none()));
                    assert!(!query.distinct || (query.limit, query.offset) == (None, None));
                }
                Input::Groups(tree) if !tree.postgres => sqlite_queries += 1,
                _ => {}
            }
        }
        assert!(
            sqlite_queries > 1000,
            "too few sqlite queries to exercise the generator"
        );
    }

    /// Diesel spells an empty `NOT IN` as `1=1`, which sqlite folds so that it never evaluates
    /// the json path `''` it would reject. The reference must fold alike.
    #[test]
    fn an_empty_list_guards_an_operand_as_diesel_spells_it() {
        let query = Query {
            postgres: false,
            distinct: false,
            int: *a(),
            text: *s(),
            bool: Bool::Or(
                boolean(Bool::In {
                    negated: true,
                    value: a(),
                    list: Vec::new(),
                }),
                boolean(Bool::CompareText(
                    Comparison::Eq,
                    text(Text::JsonField(
                        Box::new(Json::Column),
                        JsonKey::Text(text(Text::Literal(String::new()))),
                    )),
                    s(),
                )),
            ),
            filter: None,
            order: None,
            limit: None,
            offset: None,
        };
        assert_oracles_pass(&query);
    }

    #[test]
    fn postgres_oracle_catches_a_lost_parenthesis() {
        let query = Query {
            postgres: false,
            distinct: false,
            int: right_nested(),
            text: Text::Column(TextColumn::S),
            bool: Bool::Column,
            filter: None,
            order: None,
            limit: None,
            offset: None,
        };
        let faithful =
            r#"SELECT ("t"."a" - ("t"."b" - $1)), "t"."s", "t"."f" FROM "t" ORDER BY "t"."id""#;
        pg::compare(faithful.to_owned(), &query).expect("the faithful spelling");
        let lost = r#"SELECT "t"."a" - "t"."b" - $1, "t"."s", "t"."f" FROM "t" ORDER BY "t"."id""#;
        assert!(matches!(
            pg::compare(lost.to_owned(), &query),
            Err(pg::Violation::Nesting { .. })
        ));
    }
}
