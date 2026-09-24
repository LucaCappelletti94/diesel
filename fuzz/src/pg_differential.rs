//! Diesel's postgres decoders checked against `postgres-types`, an independent implementation of
//! the same binary wire formats.

use std::any::{Any, TypeId};
use std::fmt::Debug;
use std::time::SystemTime;

use bytes::BytesMut;
use chrono::{DateTime, NaiveDate, NaiveDateTime, NaiveTime, Utc};
use cidr::{IpCidr, IpInet};
use diesel::deserialize::FromSql;
use diesel::pg::{Pg, PgMetadataLookup, PgTypeMetadata, PgValue};
use diesel::query_builder::BindCollector;
use diesel::query_builder::bind_collector::RawBytesBindCollector;
use diesel::serialize::ToSql;
use diesel::sql_types::{
    Array, BigInt, Binary, Bool, CChar, Cidr, Date, Double, Float, HasSqlType, Inet, Integer, Json,
    Jsonb, MacAddr, Nullable, Oid, PgLsn, SmallInt, Text, Time, Timestamp, Timestamptz, Uuid,
};
use eui48::MacAddress;
use ipnet::IpNet;
use ipnetwork::IpNetwork;
use postgres_types::{Kind, Type};
use serde_json::Value;
use time::{OffsetDateTime, PrimitiveDateTime};

#[derive(Debug, thiserror::Error)]
pub enum Violation {
    #[error(
        "`{case}` decodes {bytes:02X?} differently\n  diesel: {diesel}\n  postgres-types: {postgres}"
    )]
    Disagree {
        case: &'static str,
        bytes: Vec<u8>,
        diesel: String,
        postgres: String,
    },
    #[error(
        "`{case}` rejects {bytes:02X?}, which postgres-types reads as {postgres}\n  diesel: {error}"
    )]
    RejectsValid {
        case: &'static str,
        bytes: Vec<u8>,
        postgres: String,
        error: String,
    },
    #[error(
        "`{case}` writes {value} as {bytes:02X?}, which postgres-types reads back as {postgres}"
    )]
    WritesWrong {
        case: &'static str,
        value: String,
        bytes: Vec<u8>,
        postgres: String,
    },
}

/// Built-in types carry a static oid, so encoding them never looks a type up.
struct NoLookup;

impl PgMetadataLookup for NoLookup {
    fn lookup_type(&mut self, type_name: &str, _: Option<&str>) -> PgTypeMetadata {
        unreachable!("built-in type encoded through a lookup of `{type_name}`")
    }

    fn as_any<'a>(&mut self) -> &mut (dyn Any + 'a)
    where
        Self: 'a,
    {
        self
    }
}

fn decode<ST, D>(bytes: &[u8], ty: &Type) -> diesel::deserialize::Result<D>
where
    D: FromSql<ST, Pg>,
{
    let oid = std::num::NonZeroU32::new(ty.oid()).expect("built-in types have an oid");
    D::from_sql(PgValue::new(bytes, &oid))
}

/// Diesel's encoding of `value`, or `None` when diesel refuses to write it.
fn encode<ST, D>(value: &D) -> Option<Vec<u8>>
where
    Pg: HasSqlType<ST>,
    D: ToSql<ST, Pg>,
{
    let mut collector = RawBytesBindCollector::<Pg>::new();
    collector
        .push_bound_value::<ST, D>(value, &mut NoLookup)
        .ok()?;
    collector.binds.pop().flatten()
}

/// postgres-types reserves room for the element count an array header claims before reading any
/// element, so a header claiming more elements than the value can hold would abort the process.
/// Such a value only reaches diesel. Every element takes at least its 4 byte length word.
fn oracle_can_read(ty: &Type, bytes: &[u8]) -> bool {
    if !matches!(ty.kind(), Kind::Array(_)) {
        return true;
    }
    let word = |at: usize| {
        bytes
            .get(at..at + 4)
            .map(|b| i32::from_be_bytes(b.try_into().expect("four bytes")))
    };
    let Some(dimensions) = word(0) else {
        return true;
    };
    let Ok(dimensions) = usize::try_from(dimensions) else {
        return true;
    };
    let mut elements: u64 = if dimensions == 0 { 0 } else { 1 };
    for dimension in 0..dimensions {
        let Some(length) = word(12 + 8 * dimension) else {
            return true;
        };
        let Ok(length) = u64::try_from(length) else {
            return true;
        };
        elements = elements.saturating_mul(length);
    }
    let header = 12 + 8 * dimensions as u64;
    elements <= (bytes.len() as u64).saturating_sub(header) / 4
}

/// postgres-types overflows re-encoding the `-infinity` timestamp it reads as a `SystemTime`.
fn oracle_can_write<P: 'static>(read: &[u8]) -> bool {
    TypeId::of::<P>() != TypeId::of::<SystemTime>() || read != i64::MIN.to_be_bytes()
}

/// Feeds `bytes` to both decoders, then feeds each decoder what the other side's encoder writes
/// for the value it read, and requires the two to agree throughout.
fn check<ST, D, P>(
    case: &'static str,
    ty: &Type,
    bytes: &[u8],
    agree: fn(&D, &P) -> bool,
) -> Result<(), Violation>
where
    Pg: HasSqlType<ST>,
    D: FromSql<ST, Pg> + ToSql<ST, Pg> + Debug,
    P: for<'a> postgres_types::FromSql<'a> + postgres_types::ToSql + Debug + 'static,
{
    let diesel = decode::<ST, D>(bytes, ty);
    let postgres = oracle_can_read(ty, bytes).then(|| P::from_sql(ty, bytes));

    if let (Ok(d), Some(Ok(p))) = (&diesel, &postgres)
        && !agree(d, p)
    {
        return Err(Violation::Disagree {
            case,
            bytes: bytes.to_vec(),
            diesel: format!("{d:?}"),
            postgres: format!("{p:?}"),
        });
    }

    // what a server writes for the value postgres-types read, diesel must read the same way
    if let Some(Ok(p)) = &postgres
        && oracle_can_write::<P>(bytes)
    {
        let mut canonical = BytesMut::new();
        if p.to_sql(ty, &mut canonical).is_ok() {
            // postgres-types writes the `is_cidr` flag as 0, PostgreSQL's `cidr_send` writes 1
            if *ty == Type::CIDR {
                canonical[2] = 1;
            }
            match decode::<ST, D>(&canonical, ty) {
                Ok(d) if agree(&d, p) => {}
                Ok(d) => {
                    return Err(Violation::Disagree {
                        case,
                        bytes: canonical.to_vec(),
                        diesel: format!("{d:?}"),
                        postgres: format!("{p:?}"),
                    });
                }
                Err(error) => {
                    return Err(Violation::RejectsValid {
                        case,
                        bytes: canonical.to_vec(),
                        postgres: format!("{p:?}"),
                        error: error.to_string(),
                    });
                }
            }
        }
    }

    // what diesel writes for the value it read, postgres-types must read back unchanged
    if let Ok(d) = &diesel
        && let Some(written) = encode::<ST, D>(d)
        && oracle_can_read(ty, &written)
    {
        let read = P::from_sql(ty, &written);
        if !read.as_ref().is_ok_and(|p| agree(d, p)) {
            return Err(Violation::WritesWrong {
                case,
                value: format!("{d:?}"),
                bytes: written,
                postgres: match read {
                    Ok(p) => format!("{p:?}"),
                    Err(error) => format!("an error, {error}"),
                },
            });
        }
    }
    Ok(())
}

macro_rules! cases {
    ( $( ($name:literal, $ST:ty, $D:ty, $P:ty, $ty:expr, $agree:expr) ),* $(,)? ) => {
        pub const CASES: &[&str] = &[ $( $name ),* ];

        pub fn check_case(selector: u8, bytes: &[u8]) -> Result<(), Violation> {
            match CASES[usize::from(selector) % CASES.len()] {
                $( $name => check::<$ST, $D, $P>($name, &$ty, bytes, $agree), )*
                _ => unreachable!(),
            }
        }
    };
}

cases!(
    ("bool", Bool, bool, bool, Type::BOOL, |d, p| d == p),
    ("i16", SmallInt, i16, i16, Type::INT2, |d, p| d == p),
    ("i32", Integer, i32, i32, Type::INT4, |d, p| d == p),
    ("i64", BigInt, i64, i64, Type::INT8, |d, p| d == p),
    ("oid", Oid, u32, u32, Type::OID, |d, p| d == p),
    ("f32", Float, f32, f32, Type::FLOAT4, |d, p| d.to_bits() == p.to_bits()),
    ("f64", Double, f64, f64, Type::FLOAT8, |d, p| d.to_bits() == p.to_bits()),
    ("text", Text, String, String, Type::TEXT, |d, p| d == p),
    ("cchar", CChar, u8, i8, Type::CHAR, |d, p| *d == p.to_ne_bytes()[0]),
    ("bytea", Binary, Vec<u8>, Vec<u8>, Type::BYTEA, |d, p| d == p),
    ("chrono_timestamp", Timestamp, NaiveDateTime, NaiveDateTime, Type::TIMESTAMP, |d, p| d == p),
    ("chrono_timestamptz", Timestamptz, DateTime<Utc>, DateTime<Utc>, Type::TIMESTAMPTZ, |d, p| d == p),
    ("chrono_date", Date, NaiveDate, NaiveDate, Type::DATE, |d, p| d == p),
    ("chrono_time", Time, NaiveTime, NaiveTime, Type::TIME, |d, p| d == p),
    ("time_timestamp", Timestamp, PrimitiveDateTime, PrimitiveDateTime, Type::TIMESTAMP, |d, p| d == p),
    ("time_timestamptz", Timestamptz, OffsetDateTime, OffsetDateTime, Type::TIMESTAMPTZ, |d, p| d == p),
    ("time_date", Date, time::Date, time::Date, Type::DATE, |d, p| d == p),
    ("time_time", Time, time::Time, time::Time, Type::TIME, |d, p| d == p),
    ("system_time", Timestamp, SystemTime, SystemTime, Type::TIMESTAMP, |d, p| d == p),
    ("uuid", Uuid, uuid::Uuid, uuid::Uuid, Type::UUID, |d, p| d == p),
    ("json", Json, Value, Value, Type::JSON, |d, p| d == p),
    ("jsonb", Jsonb, Value, Value, Type::JSONB, |d, p| d == p),
    ("inet_ipnetwork", Inet, IpNetwork, IpInet, Type::INET, |d, p| {
        d.ip() == p.address() && d.prefix() == p.network_length()
    }),
    ("inet_ipnet", Inet, IpNet, IpInet, Type::INET, |d, p| {
        d.addr() == p.address() && d.prefix_len() == p.network_length()
    }),
    // diesel writes a cidr with its host bits cleared, so a cidr stands for its network
    ("cidr_ipnetwork", Cidr, IpNetwork, IpCidr, Type::CIDR, |d, p| {
        d.network() == p.first_address() && d.prefix() == p.network_length()
    }),
    ("cidr_ipnet", Cidr, IpNet, IpCidr, Type::CIDR, |d, p| {
        d.network() == p.first_address() && d.prefix_len() == p.network_length()
    }),
    ("macaddr", MacAddr, [u8; 6], MacAddress, Type::MACADDR, |d, p| d == p.as_bytes()),
    ("pg_lsn", PgLsn, diesel::pg::data_types::PgLsn, postgres_types::PgLsn, Type::PG_LSN, |d, p| {
        d.0 == u64::from(*p)
    }),
    ("int4_array", Array<Integer>, Vec<i32>, Vec<i32>, Type::INT4_ARRAY, |d, p| d == p),
    ("text_array", Array<Nullable<Text>>, Vec<Option<String>>, Vec<Option<String>>, Type::TEXT_ARRAY, |d, p| d == p),
);
