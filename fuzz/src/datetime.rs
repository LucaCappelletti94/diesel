//! Sqlite text dates, decoded by both the `chrono` and `time` impls.

use crate::differential::{Decoded, Nanos, Violation, Ymd, compare, unrestricted};
use crate::sqlite::decode_text_as;
use diesel::SqliteConnection;
use diesel::sql_types::{Date, Time, Timestamp, TimestamptzSqlite};

pub fn check_text(conn: &mut SqliteConnection, text: &str) -> Option<Violation> {
    let violation = date(conn, text)
        .or_else(|| time_of_day(conn, text))
        .or_else(|| timestamp(conn, text))
        .or_else(|| timestamptz(conn, text))?;
    (!explains_text_divergence(text, &violation)).then_some(violation)
}

/// The three reported defects, and nothing wider: a julian day, which the two
/// impls round differently; a text only one of them parses, since they carry
/// different format lists; and an offset past ±23:59, which only one applies.
/// Delete with the fix.
pub fn explains_text_divergence(text: &str, violation: &Violation) -> bool {
    match violation {
        Violation::Differential { .. } => is_julian_day(text) || has_unusable_offset(text),
        Violation::Asymmetric { .. } => true,
        Violation::ValueRoundTrip { .. } => false,
    }
}

/// Sqlite reads a bare number as a julian day.
pub fn is_julian_day(text: &str) -> bool {
    text.trim().parse::<f64>().is_ok()
}

/// An offset no calendar accepts, such as `+24:00`.
pub fn has_unusable_offset(text: &str) -> bool {
    let Some((_, offset)) = text.trim().rsplit_once(['+', '-']) else {
        return false;
    };
    let hours = offset.split(':').next().unwrap_or_default();
    hours.parse::<u32>().is_ok_and(|hours| hours > 23)
}

fn key<ST, T, K>(
    conn: &mut SqliteConnection,
    text: &str,
    into_key: impl FnOnce(T) -> K,
) -> Decoded<K>
where
    ST: diesel::sql_types::SqlType
        + diesel::expression::TypedExpressionType
        + diesel::sql_types::SingleValue
        + diesel::query_builder::QueryId,
    diesel::sqlite::Sqlite: diesel::sql_types::HasSqlType<ST>,
    T: diesel::deserialize::FromSqlRow<ST, diesel::sqlite::Sqlite> + 'static,
{
    decode_text_as::<ST, T>(conn, text)
        .map(into_key)
        .map_err(|error| error.to_string())
}

fn date(conn: &mut SqliteConnection, text: &str) -> Option<Violation> {
    let chrono = key::<Date, chrono::NaiveDate, _>(conn, text, Ymd::from_chrono);
    let time = key::<Date, time::Date, _>(conn, text, Ymd::from_time);
    compare(
        "sqlite date text",
        ("chrono", chrono),
        ("time", time),
        Ymd::outside_time_calendar,
    )
}

fn time_of_day(conn: &mut SqliteConnection, text: &str) -> Option<Violation> {
    let chrono = key::<Time, chrono::NaiveTime, _>(conn, text, Nanos::from_chrono_time);
    let time = key::<Time, time::Time, _>(conn, text, Nanos::from_time_time);
    compare(
        "sqlite time text",
        ("chrono", chrono),
        ("time", time),
        unrestricted,
    )
}

fn timestamp(conn: &mut SqliteConnection, text: &str) -> Option<Violation> {
    let chrono =
        key::<Timestamp, chrono::NaiveDateTime, _>(conn, text, Nanos::from_chrono_datetime);
    let time = key::<Timestamp, time::PrimitiveDateTime, _>(conn, text, Nanos::from_time_primitive);
    compare(
        "sqlite timestamp text",
        ("chrono", chrono),
        ("time", time),
        Nanos::outside_time_calendar,
    )
}

fn timestamptz(conn: &mut SqliteConnection, text: &str) -> Option<Violation> {
    let chrono = key::<TimestamptzSqlite, chrono::DateTime<chrono::Utc>, _>(
        conn,
        text,
        Nanos::from_chrono_utc,
    );
    let time =
        key::<TimestamptzSqlite, time::OffsetDateTime, _>(conn, text, Nanos::from_time_offset);
    compare(
        "sqlite timestamptz text",
        ("chrono", chrono),
        ("time", time),
        Nanos::outside_time_calendar,
    )
}
