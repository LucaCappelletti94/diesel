//! Comparing two libraries decoding the same bytes.

use std::fmt::{self, Display};
use std::net::IpAddr;

/// A cross-library finding; the variant is its class.
#[derive(Debug, thiserror::Error)]
pub enum Violation {
    #[error("{case}: {left} decoded {left_value}, {right} decoded {right_value}")]
    Differential {
        case: &'static str,
        left: &'static str,
        right: &'static str,
        left_value: String,
        right_value: String,
    },
    #[error("{case}: {accepted} decoded {value}, {rejected} refused the same bytes: {error}")]
    Asymmetric {
        case: &'static str,
        accepted: &'static str,
        rejected: &'static str,
        value: String,
        error: String,
    },
    #[error("{case}: {value} does not survive a {via} round trip, got {back}")]
    ValueRoundTrip {
        case: &'static str,
        via: &'static str,
        value: String,
        back: String,
    },
}

/// A decoded value, or the message of the decoder that refused it.
pub type Decoded<K> = Result<K, String>;

/// Compares two decoders of the same bytes; `explained` names the values a
/// library legitimately refuses because its own range stops short.
pub fn compare<K: PartialEq + Display>(
    case: &'static str,
    (left_name, left): (&'static str, Decoded<K>),
    (right_name, right): (&'static str, Decoded<K>),
    explained: impl Fn(&K) -> bool,
) -> Option<Violation> {
    match (left, right) {
        (Ok(left), Ok(right)) if left == right => None,
        (Ok(left), Ok(right)) => Some(Violation::Differential {
            case,
            left: left_name,
            right: right_name,
            left_value: left.to_string(),
            right_value: right.to_string(),
        }),
        (Ok(value), Err(error)) => {
            asymmetric(case, left_name, right_name, &value, error, explained)
        }
        (Err(error), Ok(value)) => {
            asymmetric(case, right_name, left_name, &value, error, explained)
        }
        (Err(_), Err(_)) => None,
    }
}

fn asymmetric<K: Display>(
    case: &'static str,
    accepted: &'static str,
    rejected: &'static str,
    value: &K,
    error: String,
    explained: impl Fn(&K) -> bool,
) -> Option<Violation> {
    (!explained(value)).then(|| Violation::Asymmetric {
        case,
        accepted,
        rejected,
        value: value.to_string(),
        error,
    })
}

/// For keys both libraries cover completely, where any asymmetry is a finding.
pub fn unrestricted<K>(_: &K) -> bool {
    false
}

/// A calendar date, as either library reports it.
#[derive(Debug, PartialEq, Eq)]
pub struct Ymd {
    year: i32,
    month: u8,
    day: u8,
}

impl Ymd {
    pub fn from_chrono(date: chrono::NaiveDate) -> Self {
        use chrono::Datelike;
        Self {
            year: date.year(),
            month: month_of(date.month()),
            day: day_of(date.day()),
        }
    }

    pub fn from_time(date: time::Date) -> Self {
        Self {
            year: date.year(),
            month: u8::from(date.month()),
            day: date.day(),
        }
    }

    /// `time` stops at ±9999 without `large-dates`, chrono reaches ±262143.
    pub fn outside_time_calendar(&self) -> bool {
        !(time::Date::MIN.year()..=time::Date::MAX.year()).contains(&self.year)
    }
}

impl Display for Ymd {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}-{:02}-{:02}", self.year, self.month, self.day)
    }
}

/// Nanoseconds from an epoch both libraries share.
#[derive(Debug, PartialEq, Eq)]
pub struct Nanos(i128);

impl Nanos {
    pub fn from_chrono_utc(datetime: chrono::DateTime<chrono::Utc>) -> Self {
        Self(
            i128::from(datetime.timestamp()) * 1_000_000_000
                + i128::from(datetime.timestamp_subsec_nanos()),
        )
    }

    pub fn from_chrono_datetime(datetime: chrono::NaiveDateTime) -> Self {
        Self::from_chrono_utc(datetime.and_utc())
    }

    pub fn from_time_offset(datetime: time::OffsetDateTime) -> Self {
        Self(datetime.unix_timestamp_nanos())
    }

    pub fn from_time_primitive(datetime: time::PrimitiveDateTime) -> Self {
        Self::from_time_offset(datetime.assume_utc())
    }

    pub fn from_chrono_time(time: chrono::NaiveTime) -> Self {
        use chrono::Timelike;
        Self(
            i128::from(time.num_seconds_from_midnight()) * 1_000_000_000
                + i128::from(time.nanosecond()),
        )
    }

    pub fn from_time_time(time: time::Time) -> Self {
        let (hour, minute, second, nanosecond) = time.as_hms_nano();
        let seconds = i128::from(hour) * 3600 + i128::from(minute) * 60 + i128::from(second);
        Self(seconds * 1_000_000_000 + i128::from(nanosecond))
    }

    /// Only meaningful for a timestamp key; a time of day is always in range.
    pub fn outside_time_calendar(&self) -> bool {
        let min = time::PrimitiveDateTime::MIN
            .assume_utc()
            .unix_timestamp_nanos();
        let max = time::PrimitiveDateTime::MAX
            .assume_utc()
            .unix_timestamp_nanos();
        !(min..=max).contains(&self.0)
    }
}

impl Display for Nanos {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} ns", self.0)
    }
}

/// An address and the prefix length that came with it.
#[derive(Debug, PartialEq, Eq)]
pub struct Net {
    addr: IpAddr,
    prefix: u8,
}

impl Net {
    pub fn new(addr: IpAddr, prefix: u8) -> Self {
        Self { addr, prefix }
    }
}

impl Display for Net {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}/{}", self.addr, self.prefix)
    }
}

fn month_of(month: u32) -> u8 {
    u8::try_from(month).expect("a month is 1..=12")
}

fn day_of(day: u32) -> u8 {
    u8::try_from(day).expect("a day is 1..=31")
}
