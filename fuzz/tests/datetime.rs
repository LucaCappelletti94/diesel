use diesel::sql_types::{Time, Timestamp, TimestamptzSqlite};
use diesel_fuzz::datetime::{check_text, has_unusable_offset, is_julian_day};
use diesel_fuzz::sqlite::{decode_text_as, with_conn};

#[test]
fn iso_text_agrees_between_chrono_and_time() {
    with_conn(|conn| {
        for text in [
            "2026-09-03",
            "2026-09-03 12:34:56",
            "2026-09-03T12:34:56.123456",
            "12:34:56",
            "2451545.0",
        ] {
            assert!(check_text(conn, text).is_none(), "{text}");
        }
    });
}

/// Witness; delete with the fix.
#[test]
fn julian_text_rounds_differently() {
    with_conn(|conn| {
        assert_eq!(
            decode_text_as::<Timestamp, chrono::NaiveDateTime>(conn, ".2")
                .unwrap()
                .to_string(),
            "-4713-11-24 16:48:01"
        );
        assert!(is_julian_day(".2"));
        // skipped as a julian day, so ISO text stays under test
        assert!(check_text(conn, ".2").is_none());
    });
}

/// Witness; delete with the fix.
#[test]
fn julian_text_differs_below_the_microsecond() {
    with_conn(|conn| {
        let text = "2451545.123456789";
        assert_eq!(
            decode_text_as::<Timestamp, chrono::NaiveDateTime>(conn, text)
                .unwrap()
                .to_string(),
            "2000-01-01 14:57:46.666585206"
        );
        assert_eq!(
            decode_text_as::<Timestamp, time::PrimitiveDateTime>(conn, text)
                .unwrap()
                .to_string(),
            "2000-01-01 14:57:46.666585216"
        );
        assert!(is_julian_day(text));
        assert!(check_text(conn, text).is_none());
    });
}

/// Witness; delete with the fix.
#[test]
fn a_one_digit_minute_is_refused_only_by_time() {
    with_conn(|conn| {
        assert_eq!(
            decode_text_as::<Time, chrono::NaiveTime>(conn, "12:3")
                .unwrap()
                .to_string(),
            "12:03:00"
        );
        assert!(decode_text_as::<Time, time::Time>(conn, "12:3").is_err());
        assert!(!is_julian_day("12:3"));
        // the format lists differ, so an asymmetry here is the reported defect
        assert!(check_text(conn, "12:3").is_none());
    });
}

/// Witness; delete with the fix.
#[test]
fn an_offset_past_the_day_is_applied_by_only_one_impl() {
    with_conn(|conn| {
        let text = "2026-09-03 12:34:56+24:00";
        let chrono = decode_text_as::<TimestamptzSqlite, chrono::DateTime<chrono::Utc>>(conn, text)
            .expect("chrono reads it");
        let time = decode_text_as::<TimestamptzSqlite, time::OffsetDateTime>(conn, text)
            .expect("time reads it");
        assert_eq!(
            chrono.timestamp() - time.unix_timestamp(),
            86_400,
            "a whole day apart"
        );
        assert!(has_unusable_offset(text));
        assert!(check_text(conn, text).is_none());
        assert!(!has_unusable_offset("2026-09-03 12:34:56+02:00"));
    });
}
