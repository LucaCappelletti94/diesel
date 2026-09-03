//! Postgres `FromSql` dispatch: exercises every pure-byte decoder.

use std::num::NonZeroU32;
use std::ops::Bound;

use bigdecimal::BigDecimal;
use chrono::{DateTime, NaiveDate, NaiveDateTime, NaiveTime, Utc};
use diesel::deserialize::FromSql;
use diesel::pg::data_types::{
    PgDate, PgInterval, PgLsn as PgLsnValue, PgMoney, PgNumeric, PgTime, PgTimestamp,
};
use diesel::pg::{Pg, PgValue};
use diesel::sql_types::{
    Array, BigInt, Binary, Bool, Cidr, Date, Double, Float, Inet, Integer, Interval, Json, Jsonb,
    MacAddr, MacAddr8, Money, Multirange, Nullable, Numeric, Oid, PgLsn, Range, Record, SmallInt,
    Text, Time, Timestamp, Timestamptz, Uuid,
};
use ipnet::IpNet;
use ipnetwork::IpNetwork;
use time::{OffsetDateTime, PrimitiveDateTime};

use crate::differential::{Decoded, Nanos, Net, Violation, Ymd, compare, unrestricted};

/// Decodes `bytes` as `T` via `FromSql<ST, Pg>`.
fn decode<ST, T>(bytes: &[u8], oid: NonZeroU32) -> diesel::deserialize::Result<T>
where
    T: FromSql<ST, Pg>,
{
    T::from_sql(PgValue::new(bytes, &oid))
}

// one macro call, so CASES and the dispatcher cannot drift apart
macro_rules! define_cases {
    ( $( ($name:literal, $ST:ty, $T:ty) ),* $(,)? ) => {
        /// Case names; the index is the selector.
        pub const CASES: &[&str] = &[ $( $name ),* ];

        /// Decodes with the selected case; a panic is the finding.
        pub fn decode_case(selector: u8, oid: NonZeroU32, bytes: &[u8]) {
            let case = CASES[usize::from(selector) % CASES.len()];
            if skip(case, oid, bytes) {
                return;
            }
            match case {
                $( $name => { let _ = decode::<$ST, $T>(bytes, oid); } )*
                _ => unreachable!(),
            }
        }
    };
}

define_cases!(
    ("bool",               Bool,                        bool),
    ("i16",                SmallInt,                    i16),
    ("i32",                Integer,                     i32),
    ("i64",                BigInt,                      i64),
    ("u32",                Oid,                         u32),
    ("f32",                Float,                       f32),
    ("f64",                Double,                      f64),
    ("text",               Text,                        String),
    ("binary",             Binary,                      Vec<u8>),
    ("pg_numeric",         Numeric,                     PgNumeric),
    ("bigdecimal",         Numeric,                     BigDecimal),
    ("pg_money",           Money,                       PgMoney),
    ("pg_timestamp",       Timestamp,                   PgTimestamp),
    ("chrono_naive_dt",    Timestamp,                   NaiveDateTime),
    ("time_primitive_dt",  Timestamp,                   PrimitiveDateTime),
    ("chrono_naive_dt_tz", Timestamptz,                 NaiveDateTime),
    ("chrono_dt_utc",      Timestamptz,                 DateTime<Utc>),
    ("time_prim_dt_tz",    Timestamptz,                 PrimitiveDateTime),
    ("time_offset_dt",     Timestamptz,                 OffsetDateTime),
    ("pg_date",            Date,                        PgDate),
    ("chrono_date",        Date,                        NaiveDate),
    ("time_date",          Date,                        time::Date),
    ("pg_time",            Time,                        PgTime),
    ("chrono_time",        Time,                        NaiveTime),
    ("time_time",          Time,                        time::Time),
    ("pg_interval",        Interval,                    PgInterval),
    ("chrono_interval",    Interval,                    chrono::Duration),
    ("uuid",               Uuid,                        uuid::Uuid),
    ("inet_ipnet",         Inet,                        IpNet),
    ("inet_ipnetwork",     Inet,                        IpNetwork),
    ("cidr_ipnet",         Cidr,                        IpNet),
    ("cidr_ipnetwork",     Cidr,                        IpNetwork),
    ("mac_addr",           MacAddr,                     [u8; 6]),
    ("mac_addr8",          MacAddr8,                    [u8; 8]),
    ("pg_lsn",             PgLsn,                       PgLsnValue),
    ("json",               Json,                        serde_json::Value),
    ("jsonb",              Jsonb,                       serde_json::Value),
    ("array_i32",          Array<Integer>,              Vec<i32>),
    ("array_opt_text",     Array<Nullable<Text>>,       Vec<Option<String>>),
    ("range_i32",          Range<Integer>,              (Bound<i32>, Bound<i32>)),
    ("multirange_i32",     Multirange<Integer>,         Vec<(Bound<i32>, Bound<i32>)>),
    ("record",             Record<(Integer, Text)>,     (i32, String)),
);

/// The reported panics, each narrowed to the bytes that trigger it.
pub fn known_panic(case: &str, bytes: &[u8]) -> bool {
    match case {
        // PgInterval::from_sql slices unchecked (pg/types/date_and_time/mod.rs:177)
        "pg_interval" => bytes.len() < 16,
        // chrono::Duration multiplies months by 30 in i32 (chrono.rs:207)
        "chrono_interval" => bytes.len() < 16 || interval_days_overflow(bytes),
        _ => false,
    }
}

/// Skips what this input cannot say anything about: a reported panic, or a
/// rescaling that would allocate megabytes rather than reach new code.
fn skip(case: &str, oid: NonZeroU32, bytes: &[u8]) -> bool {
    known_panic(case, bytes)
        || (case == "bigdecimal"
            && !decode::<Numeric, PgNumeric>(bytes, oid).is_ok_and(|n| numeric_is_bounded(&n)))
}

fn interval_days_overflow(bytes: &[u8]) -> bool {
    let field = |range: std::ops::Range<usize>| {
        i32::from_be_bytes(bytes[range].try_into().expect("four bytes"))
    };
    field(12..16)
        .checked_mul(30)
        .and_then(|days| days.checked_add(field(8..12)))
        .is_none()
}

/// The cases carrying a cross-library property, with the function that checks
/// each; the index is the selector.
type DifferentialCase = (&'static str, fn(NonZeroU32, &[u8]) -> Option<Violation>);

pub const DIFFERENTIAL_CASES: &[DifferentialCase] = &[
    ("pg_numeric", diff_numeric),
    ("chrono_naive_dt", diff_timestamp),
    ("chrono_dt_utc", diff_timestamptz),
    ("chrono_date", diff_date),
    ("chrono_time", diff_time),
    ("inet_ipnet", diff_inet),
    ("cidr_ipnet", diff_cidr),
];

/// Checks the property of `DIFFERENTIAL_CASES[selector % DIFFERENTIAL_CASES.len()]`.
pub fn differential(selector: u8, oid: NonZeroU32, bytes: &[u8]) -> Option<Violation> {
    let (_, check) = DIFFERENTIAL_CASES[usize::from(selector) % DIFFERENTIAL_CASES.len()];
    check(oid, bytes)
}

/// The conversion rescales by `10^(4 * weight + scale)`, so an unbounded wire
/// value allocates megabytes and `From<&BigDecimal>` panics past `u16` groups.
fn numeric_is_bounded(numeric: &PgNumeric) -> bool {
    let (weight, scale, digits) = match numeric {
        PgNumeric::Positive {
            weight,
            scale,
            digits,
        }
        | PgNumeric::Negative {
            weight,
            scale,
            digits,
        } => (*weight, *scale, digits),
        PgNumeric::NaN => return false,
    };
    digits.len() <= 64 && weight.unsigned_abs() <= 64 && scale <= 64
}

/// `PgNumeric` through `BigDecimal` and back must be a fixed point.
fn diff_numeric(oid: NonZeroU32, bytes: &[u8]) -> Option<Violation> {
    let Ok(numeric) = decode::<Numeric, PgNumeric>(bytes, oid) else {
        return None;
    };
    if !numeric_is_bounded(&numeric) {
        return None;
    }
    let Ok(decimal) = BigDecimal::try_from(&numeric) else {
        return None;
    };
    let Ok(back) = BigDecimal::try_from(PgNumeric::from(&decimal)) else {
        return None;
    };
    if decimal != back {
        Some(Violation::ValueRoundTrip {
            case: "pg numeric",
            via: "BigDecimal",
            value: decimal.to_string(),
            back: back.to_string(),
        })
    } else {
        None
    }
}

fn key<ST, T, K>(bytes: &[u8], oid: NonZeroU32, into_key: impl FnOnce(T) -> K) -> Decoded<K>
where
    T: FromSql<ST, Pg>,
{
    decode::<ST, T>(bytes, oid)
        .map(into_key)
        .map_err(|error| error.to_string())
}

/// chrono and time must agree on `Timestamp`.
fn diff_timestamp(oid: NonZeroU32, bytes: &[u8]) -> Option<Violation> {
    compare(
        "pg timestamp",
        (
            "chrono",
            key::<Timestamp, NaiveDateTime, _>(bytes, oid, Nanos::from_chrono_datetime),
        ),
        (
            "time",
            key::<Timestamp, PrimitiveDateTime, _>(bytes, oid, Nanos::from_time_primitive),
        ),
        Nanos::outside_time_calendar,
    )
}

/// chrono and time must agree on `Timestamptz`.
fn diff_timestamptz(oid: NonZeroU32, bytes: &[u8]) -> Option<Violation> {
    compare(
        "pg timestamptz",
        (
            "chrono",
            key::<Timestamptz, DateTime<Utc>, _>(bytes, oid, Nanos::from_chrono_utc),
        ),
        (
            "time",
            key::<Timestamptz, OffsetDateTime, _>(bytes, oid, Nanos::from_time_offset),
        ),
        Nanos::outside_time_calendar,
    )
}

/// chrono and time must agree on `Date`.
fn diff_date(oid: NonZeroU32, bytes: &[u8]) -> Option<Violation> {
    compare(
        "pg date",
        (
            "chrono",
            key::<Date, NaiveDate, _>(bytes, oid, Ymd::from_chrono),
        ),
        (
            "time",
            key::<Date, time::Date, _>(bytes, oid, Ymd::from_time),
        ),
        Ymd::outside_time_calendar,
    )
}

/// chrono and time must agree on `Time`.
fn diff_time(oid: NonZeroU32, bytes: &[u8]) -> Option<Violation> {
    compare(
        "pg time",
        (
            "chrono",
            key::<Time, NaiveTime, _>(bytes, oid, Nanos::from_chrono_time),
        ),
        (
            "time",
            key::<Time, time::Time, _>(bytes, oid, Nanos::from_time_time),
        ),
        unrestricted,
    )
}

/// `ipnet` and `ipnetwork` must agree on `Inet`.
fn diff_inet(oid: NonZeroU32, bytes: &[u8]) -> Option<Violation> {
    compare(
        "pg inet",
        ("ipnet", key::<Inet, IpNet, _>(bytes, oid, net_of_ipnet)),
        (
            "ipnetwork",
            key::<Inet, IpNetwork, _>(bytes, oid, net_of_ipnetwork),
        ),
        unrestricted,
    )
}

/// `ipnet` and `ipnetwork` must agree on `Cidr`.
fn diff_cidr(oid: NonZeroU32, bytes: &[u8]) -> Option<Violation> {
    compare(
        "pg cidr",
        ("ipnet", key::<Cidr, IpNet, _>(bytes, oid, net_of_ipnet)),
        (
            "ipnetwork",
            key::<Cidr, IpNetwork, _>(bytes, oid, net_of_ipnetwork),
        ),
        unrestricted,
    )
}

fn net_of_ipnet(net: IpNet) -> Net {
    Net::new(net.addr(), net.prefix_len())
}

fn net_of_ipnetwork(net: IpNetwork) -> Net {
    Net::new(net.ip(), net.prefix())
}
