use std::num::NonZeroU32;

use diesel_fuzz::pg;

/// Every case, on empty, 1-byte and 64-byte buffers.
#[test]
fn decode_all_cases_no_panic() {
    let oid = NonZeroU32::new(1).unwrap();
    let buffers: &[&[u8]] = &[&[], &[0x00_u8], &[0xFF_u8; 64], &[0x00_u8; 64]];
    for (i, _name) in pg::CASES.iter().enumerate() {
        let selector = u8::try_from(i).expect("CASES.len() must be < 256");
        for &buf in buffers {
            pg::decode_case(selector, oid, buf);
        }
    }
}

/// A valid timestamp, so the differential property is not vacuous.
#[test]
fn timestamp_epoch_chrono_time_agree() {
    let oid = NonZeroU32::new(1).unwrap();
    assert!(
        pg::differential(selector("chrono_naive_dt"), oid, &0_i64.to_be_bytes()).is_none(),
        "chrono and time disagree on the postgres epoch timestamp"
    );
}

/// A valid date, likewise.
#[test]
fn date_epoch_chrono_time_agree() {
    let oid = NonZeroU32::new(1).unwrap();
    assert!(
        pg::differential(selector("chrono_date"), oid, &0_i32.to_be_bytes()).is_none(),
        "chrono and time disagree on the postgres epoch date"
    );
}

fn selector(case: &str) -> u8 {
    let position = pg::DIFFERENTIAL_CASES
        .iter()
        .position(|(name, _)| *name == case)
        .expect("case must exist");
    u8::try_from(position).expect("DIFFERENTIAL_CASES.len() must be < 256")
}

/// Every selector value must reach a property, not a no-op.
#[test]
fn every_differential_selector_dispatches() {
    let oid = NonZeroU32::new(1).unwrap();
    for (name, _) in pg::DIFFERENTIAL_CASES {
        assert!(pg::CASES.contains(name), "{name} is not a decode case");
    }
    for raw in 0..=u8::MAX {
        let _ = pg::differential(raw, oid, &[0x00; 16]);
    }
}

/// A date past year 9999 is representable in chrono and not in `time`.
#[test]
fn date_outside_the_time_calendar_is_explained() {
    let oid = NonZeroU32::new(1).unwrap();
    assert!(pg::differential(selector("chrono_date"), oid, &3_000_000_i32.to_be_bytes()).is_none());
}

/// Likewise for a timestamp past the `time` calendar.
#[test]
fn timestamp_outside_the_time_calendar_is_explained() {
    let oid = NonZeroU32::new(1).unwrap();
    let bytes = 253_402_300_800_000_000_i64.to_be_bytes();
    assert!(pg::differential(selector("chrono_naive_dt"), oid, &bytes).is_none());
    assert!(pg::differential(selector("chrono_dt_utc"), oid, &bytes).is_none());
}

fn interval(microseconds: i64, days: i32, months: i32) -> Vec<u8> {
    let mut bytes = microseconds.to_be_bytes().to_vec();
    bytes.extend(days.to_be_bytes());
    bytes.extend(months.to_be_bytes());
    bytes
}

/// The guard covers the reported panic, not the whole decoder.
#[test]
fn the_interval_guard_only_skips_what_panics() {
    assert!(!pg::known_panic("chrono_interval", &interval(0, 0, 0)));
    assert!(!pg::known_panic(
        "chrono_interval",
        &interval(i64::MAX, 1, 1)
    ));
    assert!(pg::known_panic(
        "chrono_interval",
        &interval(0, 0, i32::MAX)
    ));
    assert!(pg::known_panic("chrono_interval", &[]));
    assert!(!pg::known_panic("pg_interval", &interval(0, 0, 0)));
    assert!(pg::known_panic("pg_interval", &[0x00; 15]));
    assert!(!pg::known_panic("i32", &[]));
}

/// A safe interval must reach `FromSql<Interval, Pg> for chrono::Duration`.
#[test]
fn a_safe_interval_decodes_under_chrono() {
    use diesel::deserialize::FromSql;
    use diesel::pg::{Pg, PgValue};
    use diesel::sql_types::Interval;

    let oid = NonZeroU32::new(1186).expect("interval oid");
    let bytes = interval(1_000_000, 2, 3);
    let decoded = <chrono::Duration as FromSql<Interval, Pg>>::from_sql(PgValue::new(&bytes, &oid))
        .expect("a duration");
    assert_eq!(
        decoded,
        chrono::Duration::days(92) + chrono::Duration::seconds(1)
    );
    pg::decode_case(
        u8::try_from(
            pg::CASES
                .iter()
                .position(|&case| case == "chrono_interval")
                .expect("the case exists"),
        )
        .expect("CASES.len() < 256"),
        oid,
        &bytes,
    );
}

/// Witness; delete with the fix, together with its `known_panic` arm.
#[test]
fn interval_panics_on_short_buffer() {
    use diesel::deserialize::FromSql;
    use diesel::pg::data_types::PgInterval;
    use diesel::pg::{Pg, PgValue};
    use diesel::sql_types::Interval;

    let oid = NonZeroU32::new(1).unwrap();
    let result = std::panic::catch_unwind(|| {
        let _ = <PgInterval as FromSql<Interval, Pg>>::from_sql(PgValue::new(&[], &oid));
    });
    assert!(
        result.is_err(),
        "PgInterval::from_sql must panic on an empty buffer"
    );
    let result2 = std::panic::catch_unwind(|| {
        let _ = <chrono::Duration as FromSql<Interval, Pg>>::from_sql(PgValue::new(&[], &oid));
    });
    assert!(
        result2.is_err(),
        "chrono::Duration::from_sql must panic on an empty buffer"
    );
}

/// Witness; delete with the fix.
#[test]
fn chrono_interval_overflows_on_large_month_count() {
    let oid = std::num::NonZeroU32::new(1186).expect("interval oid");
    let mut bytes = vec![0u8; 8];
    bytes.extend(0i32.to_be_bytes());
    bytes.extend(i32::MAX.to_be_bytes());
    let decoded = std::panic::catch_unwind(|| {
        let _ = <chrono::Duration as diesel::deserialize::FromSql<
            diesel::sql_types::Interval,
            diesel::pg::Pg,
        >>::from_sql(diesel::pg::PgValue::new(&bytes, &oid));
    });
    assert!(decoded.is_err(), "chrono interval no longer overflows");
}
