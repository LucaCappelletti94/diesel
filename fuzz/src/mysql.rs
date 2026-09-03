//! MySQL `FromSql` dispatch table and differential properties.

use crate::differential::{Decoded, Nanos, Violation, Ymd, compare, unrestricted};
use bigdecimal::BigDecimal;
use diesel::deserialize::FromSql;
use diesel::mysql::data_types::MysqlTime;
use diesel::mysql::sql_types::Unsigned;
use diesel::mysql::{Mysql, MysqlType, MysqlValue};
use diesel::sql_types::{
    BigInt, Binary, Bool, Date, Datetime, Double, Float, Integer, Json, Numeric, SmallInt, Text,
    Time, Timestamp, TinyInt,
};

fn decode<ST, T>(bytes: &[u8], tpe: MysqlType) -> diesel::deserialize::Result<T>
where
    T: FromSql<ST, Mysql>,
{
    T::from_sql(MysqlValue::new(bytes, tpe))
}

// one macro call, so CASES and the dispatcher cannot drift apart
macro_rules! define_cases {
    ( $( ($name:literal, $ST:ty, $T:ty) ),* $(,)? ) => {
        /// Case names; `selector % CASES.len()` picks one.
        pub const CASES: &[&str] = &[ $( $name ),* ];

        /// Decodes with the selected case and wire type; a panic is the finding.
        pub fn decode_case(selector: u8, type_selector: u8, bytes: &[u8]) {
            let tpe = TYPES[usize::from(type_selector) % TYPES.len()];
            match CASES[usize::from(selector) % CASES.len()] {
                $( $name => { let _ = decode::<$ST, $T>(bytes, tpe); } )*
                _ => unreachable!(),
            }
        }
    };
}

define_cases!(
    ("i8",                        TinyInt,             i8),
    ("u8",                        Unsigned<TinyInt>,   u8),
    ("i16",                       SmallInt,            i16),
    ("u16",                       Unsigned<SmallInt>,  u16),
    ("i32",                       Integer,             i32),
    ("u32",                       Unsigned<Integer>,   u32),
    ("i64",                       BigInt,              i64),
    ("u64",                       Unsigned<BigInt>,    u64),
    ("f32",                       Float,               f32),
    ("f64",                       Double,              f64),
    ("BigDecimal",                Numeric,             BigDecimal),
    ("bool",                      Bool,                bool),
    ("String",                    Text,                String),
    ("Vec<u8>",                   Binary,              Vec<u8>),
    ("MysqlTime_date",            Date,                MysqlTime),
    ("MysqlTime_time",            Time,                MysqlTime),
    ("MysqlTime_datetime",        Datetime,            MysqlTime),
    ("MysqlTime_timestamp",       Timestamp,           MysqlTime),
    ("chrono_NaiveDate",          Date,                chrono::NaiveDate),
    ("chrono_NaiveTime",          Time,                chrono::NaiveTime),
    ("chrono_NaiveDateTime_ts",   Timestamp,           chrono::NaiveDateTime),
    ("chrono_NaiveDateTime_dt",   Datetime,            chrono::NaiveDateTime),
    ("time_Date",                 Date,                time::Date),
    ("time_Time",                 Time,                time::Time),
    ("time_PrimitiveDateTime_dt", Datetime,            time::PrimitiveDateTime),
    ("time_PrimitiveDateTime_ts", Timestamp,           time::PrimitiveDateTime),
    ("time_OffsetDateTime_dt",    Datetime,            time::OffsetDateTime),
    ("time_OffsetDateTime_ts",    Timestamp,           time::OffsetDateTime),
    ("Json",                      Json,                serde_json::Value),
);

/// Wire types; `type_selector % TYPES.len()` picks one.
pub const TYPES: &[MysqlType] = &[
    MysqlType::Tiny,
    MysqlType::UnsignedTiny,
    MysqlType::Short,
    MysqlType::UnsignedShort,
    MysqlType::Long,
    MysqlType::UnsignedLong,
    MysqlType::LongLong,
    MysqlType::UnsignedLongLong,
    MysqlType::Float,
    MysqlType::Double,
    MysqlType::Numeric,
    MysqlType::Time,
    MysqlType::Date,
    MysqlType::DateTime,
    MysqlType::Timestamp,
    MysqlType::String,
    MysqlType::Blob,
    MysqlType::Bit,
    MysqlType::Set,
    MysqlType::Enum,
];

/// The cases carrying a chrono against `time` property, with the function that
/// checks each; the index is the selector.
type DifferentialCase = (&'static str, fn(&[u8], MysqlType) -> Option<Violation>);

pub const DIFFERENTIAL_CASES: &[DifferentialCase] = &[
    ("mysql date", diff_date),
    ("mysql time", diff_time),
    ("mysql datetime", diff_datetime),
    ("mysql timestamp", diff_timestamp),
];

/// chrono and time must agree when both decode the same bytes.
pub fn differential(selector: u8, type_selector: u8, bytes: &[u8]) -> Option<Violation> {
    let tpe = TYPES[usize::from(type_selector) % TYPES.len()];
    if known_validation_split(bytes, tpe) {
        return None;
    }
    let (_, check) = DIFFERENTIAL_CASES[usize::from(selector) % DIFFERENTIAL_CASES.len()];
    check(bytes, tpe)
}

/// The reported validation splits, and nothing wider. The `time` impls check
/// every `MYSQL_TIME` field; the chrono ones read only the fields their type
/// uses. So a field outside the range a MySQL server can send, or a field the
/// case does not use, is the reported defect rather than a new one. Delete
/// with the fix.
pub fn known_validation_split(bytes: &[u8], tpe: MysqlType) -> bool {
    decode::<Datetime, MysqlTime>(bytes, tpe).is_ok_and(|value| {
        value.time_zone_displacement != 0
            || value.month > 12
            || value.day > 31
            || value.hour > 838
            || value.minute > 59
            || value.second > 59
            || value.second_part > 999_999
    })
}

/// A time of day carrying a date, which only the `time` impls refuse.
pub fn carries_date_fields(bytes: &[u8], tpe: MysqlType) -> bool {
    decode::<Datetime, MysqlTime>(bytes, tpe)
        .is_ok_and(|value| value.year != 0 || value.month != 0 || value.day != 0)
}

/// A date carrying a time of day, likewise.
pub fn carries_time_fields(bytes: &[u8], tpe: MysqlType) -> bool {
    decode::<Datetime, MysqlTime>(bytes, tpe).is_ok_and(|value| {
        value.hour != 0 || value.minute != 0 || value.second != 0 || value.second_part != 0
    })
}

fn key<ST, T, K>(bytes: &[u8], tpe: MysqlType, into_key: impl FnOnce(T) -> K) -> Decoded<K>
where
    T: FromSql<ST, Mysql>,
{
    decode::<ST, T>(bytes, tpe)
        .map(into_key)
        .map_err(|error| error.to_string())
}

fn diff_date(bytes: &[u8], tpe: MysqlType) -> Option<Violation> {
    if carries_time_fields(bytes, tpe) {
        return None;
    }
    compare(
        "mysql date",
        (
            "chrono",
            key::<Date, chrono::NaiveDate, _>(bytes, tpe, Ymd::from_chrono),
        ),
        (
            "time",
            key::<Date, time::Date, _>(bytes, tpe, Ymd::from_time),
        ),
        Ymd::outside_time_calendar,
    )
}

fn diff_time(bytes: &[u8], tpe: MysqlType) -> Option<Violation> {
    if carries_date_fields(bytes, tpe) {
        return None;
    }
    compare(
        "mysql time",
        (
            "chrono",
            key::<Time, chrono::NaiveTime, _>(bytes, tpe, Nanos::from_chrono_time),
        ),
        (
            "time",
            key::<Time, time::Time, _>(bytes, tpe, Nanos::from_time_time),
        ),
        unrestricted,
    )
}

fn diff_datetime(bytes: &[u8], tpe: MysqlType) -> Option<Violation> {
    compare(
        "mysql datetime",
        (
            "chrono",
            key::<Datetime, chrono::NaiveDateTime, _>(bytes, tpe, Nanos::from_chrono_datetime),
        ),
        (
            "time",
            key::<Datetime, time::PrimitiveDateTime, _>(bytes, tpe, Nanos::from_time_primitive),
        ),
        Nanos::outside_time_calendar,
    )
}

fn diff_timestamp(bytes: &[u8], tpe: MysqlType) -> Option<Violation> {
    compare(
        "mysql timestamp",
        (
            "chrono",
            key::<Timestamp, chrono::NaiveDateTime, _>(bytes, tpe, Nanos::from_chrono_datetime),
        ),
        (
            "time",
            key::<Timestamp, time::PrimitiveDateTime, _>(bytes, tpe, Nanos::from_time_primitive),
        ),
        Nanos::outside_time_calendar,
    )
}
