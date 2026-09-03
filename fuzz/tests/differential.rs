use diesel_fuzz::differential::Violation;
use diesel_fuzz::differential::{Nanos, Ymd, compare, unrestricted};

fn ymd(year: i32, month: u32, day: u32) -> Ymd {
    Ymd::from_chrono(chrono::NaiveDate::from_ymd_opt(year, month, day).expect("a valid date"))
}

fn nanos(seconds: i64, nanoseconds: u32) -> Nanos {
    Nanos::from_chrono_datetime(
        chrono::DateTime::from_timestamp(seconds, nanoseconds)
            .expect("a valid timestamp")
            .naive_utc(),
    )
}

#[test]
fn equal_keys_are_not_a_violation() {
    assert!(
        compare(
            "case",
            ("chrono", Ok(ymd(2026, 9, 3))),
            ("time", Ok(ymd(2026, 9, 3))),
            Ymd::outside_time_calendar,
        )
        .is_none()
    );
}

#[test]
fn unequal_keys_are_a_difference() {
    let violation = compare(
        "case",
        ("chrono", Ok(ymd(2026, 9, 3))),
        ("time", Ok(ymd(2026, 9, 4))),
        Ymd::outside_time_calendar,
    )
    .expect("a difference");
    assert!(
        matches!(violation, Violation::Differential { .. }),
        "{violation}"
    );
}

#[test]
fn one_sided_success_inside_both_calendars_is_a_violation() {
    let violation = compare(
        "case",
        ("chrono", Ok(ymd(2026, 9, 3))),
        ("time", Err("rejected".to_string())),
        Ymd::outside_time_calendar,
    )
    .expect("an asymmetry");
    assert!(
        matches!(
            &violation,
            Violation::Asymmetric { accepted, rejected, .. } if *accepted == "chrono" && *rejected == "time"
        ),
        "{violation}"
    );
}

#[test]
fn one_sided_success_is_reported_whichever_side_succeeds() {
    let violation = compare(
        "case",
        ("chrono", Err("rejected".to_string())),
        ("time", Ok(ymd(2026, 9, 3))),
        Ymd::outside_time_calendar,
    )
    .expect("an asymmetry");
    assert!(
        matches!(
            &violation,
            Violation::Asymmetric { accepted, rejected, .. } if *accepted == "time" && *rejected == "chrono"
        ),
        "{violation}"
    );
}

#[test]
fn a_year_past_the_time_calendar_explains_the_asymmetry() {
    assert!(
        compare(
            "case",
            ("chrono", Ok(ymd(10212, 1, 1))),
            ("time", Err("rejected".to_string())),
            Ymd::outside_time_calendar,
        )
        .is_none()
    );
}

#[test]
fn a_timestamp_past_the_time_calendar_explains_the_asymmetry() {
    assert!(
        compare(
            "case",
            ("chrono", Ok(nanos(253_402_300_800, 0))),
            ("time", Err("rejected".to_string())),
            Nanos::outside_time_calendar,
        )
        .is_none()
    );
}

#[test]
fn both_sides_failing_is_not_a_violation() {
    assert!(
        compare(
            "case",
            ("chrono", Err::<Ymd, _>("rejected".to_string())),
            ("time", Err("rejected".to_string())),
            Ymd::outside_time_calendar,
        )
        .is_none()
    );
}

#[test]
fn an_unrestricted_key_never_explains_an_asymmetry() {
    let violation = compare(
        "case",
        ("chrono", Ok(nanos(253_402_300_800, 0))),
        ("time", Err("rejected".to_string())),
        unrestricted,
    )
    .expect("an asymmetry");
    assert!(
        matches!(violation, Violation::Asymmetric { .. }),
        "{violation}"
    );
}

#[test]
fn nanos_separate_sub_microsecond_values() {
    let violation = compare(
        "case",
        ("chrono", Ok(nanos(0, 10))),
        ("time", Ok(nanos(0, 20))),
        Nanos::outside_time_calendar,
    )
    .expect("a difference");
    assert!(
        matches!(violation, Violation::Differential { .. }),
        "{violation}"
    );
}

#[test]
fn a_date_key_agrees_across_libraries() {
    let chrono =
        Ymd::from_chrono(chrono::NaiveDate::from_ymd_opt(2026, 9, 3).expect("a valid chrono date"));
    let time = Ymd::from_time(
        time::Date::from_calendar_date(2026, time::Month::September, 3).expect("a valid time date"),
    );
    assert_eq!(chrono, time);
}
