use core::ops::Mul;

use crate::data_types::PgInterval;

/// A DSL added to integers and `f64` to construct PostgreSQL intervals.
///
/// # Panics
///
/// These methods panic when the value has no PostgreSQL interval, which covers
/// `NAN` and `Infinity` and any count whose scaled months, days or microseconds
/// leave their field.
///
/// # Examples
///
/// ```rust
/// # include!("../../../doctest_setup.rs");
/// # use diesel::dsl::*;
/// #
/// # table! {
/// #     users {
/// #         id -> Serial,
/// #         name -> VarChar,
/// #         created_at -> Timestamp,
/// #     }
/// # }
/// #
/// # fn main() {
/// #     use self::users::dsl::*;
/// #     let connection = &mut connection_no_data();
/// #     diesel::sql_query("CREATE TABLE users (id serial primary key, name
/// #        varchar not null, created_at timestamp not null)")
/// #     .execute(connection)
/// #     .unwrap();
/// diesel::sql_query(
///     "INSERT INTO users (name, created_at) VALUES
///     ('Sean', NOW()), ('Tess', NOW() - '5 minutes'::interval),
///     ('Jim', NOW() - '10 minutes'::interval)",
/// )
/// .execute(connection)
/// .unwrap();
///
/// let mut data: Vec<String> = users
///     .select(name)
///     .filter(created_at.gt(now - 7.minutes()))
///     .load(connection)
///     .unwrap();
/// assert_eq!(2, data.len());
/// assert_eq!("Sean".to_string(), data[0]);
/// assert_eq!("Tess".to_string(), data[1]);
/// # }
/// ```
///
/// ```rust
/// # include!("../../../doctest_setup.rs");
/// # use diesel::dsl::*;
/// #
/// # table! {
/// #     users {
/// #         id -> Serial,
/// #         name -> VarChar,
/// #         created_at -> Timestamp,
/// #     }
/// # }
/// #
/// # fn main() {
/// #     use self::users::dsl::*;
/// #     let connection = &mut connection_no_data();
/// #     diesel::sql_query("CREATE TABLE users (id serial primary key, name
/// #        varchar not null, created_at timestamp not null)")
/// #     .execute(connection)
/// #     .unwrap();
/// diesel::sql_query(
///     "INSERT INTO users (name, created_at) VALUES
///     ('Sean', NOW()), ('Tess', NOW() - '5 days'::interval),
///     ('Jim', NOW() - '10 days'::interval)",
/// )
/// .execute(connection)
/// .unwrap();
///
/// let mut data: Vec<String> = users
///     .select(name)
///     .filter(created_at.gt(now - 7.days()))
///     .load(connection)
///     .unwrap();
/// assert_eq!(2, data.len());
/// assert_eq!("Sean".to_string(), data[0]);
/// assert_eq!("Tess".to_string(), data[1]);
/// # }
/// ```
#[cfg(feature = "postgres_backend")]
pub trait IntervalDsl: Sized + From<i32> + Mul<Self, Output = Self> {
    /// Returns a PgInterval representing `self` as microseconds
    fn microseconds(self) -> PgInterval;
    /// Returns a PgInterval representing `self` in days
    fn days(self) -> PgInterval;
    /// Returns a PgInterval representing `self` in months
    fn months(self) -> PgInterval;

    /// Returns a PgInterval representing `self` as milliseconds
    fn milliseconds(self) -> PgInterval {
        (self * 1000.into()).microseconds()
    }

    /// Returns a PgInterval representing `self` as seconds
    fn seconds(self) -> PgInterval {
        (self * 1000.into()).milliseconds()
    }

    /// Returns a PgInterval representing `self` as minutes
    fn minutes(self) -> PgInterval {
        (self * 60.into()).seconds()
    }

    /// Returns a PgInterval representing `self` as hours
    fn hours(self) -> PgInterval {
        (self * 60.into()).minutes()
    }

    /// Returns a PgInterval representing `self` in weeks
    ///
    /// Note: When called on a high precision float, the returned interval may
    /// be 1 microsecond different than the equivalent string passed to
    /// PostgreSQL.
    fn weeks(self) -> PgInterval {
        (self * 7.into()).days()
    }

    /// Returns a PgInterval representing `self` in weeks
    ///
    /// Note: When called on a float, this method will mimic the behavior of
    /// PostgreSQL's interval parsing, and will ignore units smaller than
    /// months.
    ///
    /// ```rust
    /// # use diesel::dsl::*;
    /// assert_eq!(1.04.years(), 1.year());
    /// assert_eq!(1.09.years(), 1.year() + 1.month());
    /// ```
    fn years(self) -> PgInterval {
        (self * 12.into()).months()
    }

    /// Identical to `microseconds`
    fn microsecond(self) -> PgInterval {
        self.microseconds()
    }

    /// Identical to `milliseconds`
    fn millisecond(self) -> PgInterval {
        self.milliseconds()
    }

    /// Identical to `seconds`
    fn second(self) -> PgInterval {
        self.seconds()
    }

    /// Identical to `minutes`
    fn minute(self) -> PgInterval {
        self.minutes()
    }

    /// Identical to `hours`
    fn hour(self) -> PgInterval {
        self.hours()
    }

    /// Identical to `days`
    fn day(self) -> PgInterval {
        self.days()
    }

    /// Identical to `weeks`
    fn week(self) -> PgInterval {
        self.weeks()
    }

    /// Identical to `months`
    fn month(self) -> PgInterval {
        self.months()
    }

    /// Identical to `years`
    fn year(self) -> PgInterval {
        self.years()
    }
}

impl IntervalDsl for i32 {
    fn microseconds(self) -> PgInterval {
        i64::from(self).microseconds()
    }

    fn days(self) -> PgInterval {
        PgInterval::from_days(self)
    }

    fn months(self) -> PgInterval {
        PgInterval::from_months(self)
    }

    fn weeks(self) -> PgInterval {
        i64::from(self).weeks()
    }

    fn years(self) -> PgInterval {
        i64::from(self).years()
    }

    fn milliseconds(self) -> PgInterval {
        i64::from(self).milliseconds()
    }

    fn seconds(self) -> PgInterval {
        i64::from(self).seconds()
    }

    fn minutes(self) -> PgInterval {
        i64::from(self).minutes()
    }

    fn hours(self) -> PgInterval {
        i64::from(self).hours()
    }
}

impl IntervalDsl for i64 {
    fn microseconds(self) -> PgInterval {
        PgInterval::from_microseconds(self)
    }

    fn days(self) -> PgInterval {
        i32::try_from(self)
            .expect("Maximal supported day interval size is 32 bit")
            .days()
    }

    fn months(self) -> PgInterval {
        i32::try_from(self)
            .expect("Maximal supported month interval size is 32 bit")
            .months()
    }

    fn milliseconds(self) -> PgInterval {
        self.checked_mul(1000)
            .expect(OVERFLOW_MICROSECONDS)
            .microseconds()
    }

    fn seconds(self) -> PgInterval {
        self.checked_mul(1000)
            .expect(OVERFLOW_MICROSECONDS)
            .milliseconds()
    }

    fn minutes(self) -> PgInterval {
        self.checked_mul(60).expect(OVERFLOW_MICROSECONDS).seconds()
    }

    fn hours(self) -> PgInterval {
        self.checked_mul(60).expect(OVERFLOW_MICROSECONDS).minutes()
    }

    fn weeks(self) -> PgInterval {
        self.checked_mul(7).expect(OVERFLOW_DAYS).days()
    }

    fn years(self) -> PgInterval {
        self.checked_mul(12).expect(OVERFLOW_MONTHS).months()
    }
}

const OVERFLOW_MICROSECONDS: &str = "Maximal supported interval size is 64 bit microseconds";
const OVERFLOW_DAYS: &str = "Maximal supported day interval size is 32 bit";
const OVERFLOW_MONTHS: &str = "Maximal supported month interval size is 32 bit";

/// Casts to `i32`, panicking rather than saturating or turning `NAN` into zero.
#[allow(clippy::cast_possible_truncation)] // the range is asserted below
fn i32_from_f64(value: f64) -> i32 {
    assert!(
        value >= f64::from(i32::MIN) && value <= f64::from(i32::MAX),
        "{OVERFLOW_DAYS}, got {value}"
    );
    value as i32
}

/// Casts to `i64`, panicking rather than saturating or turning `NAN` into zero.
#[allow(clippy::cast_possible_truncation)] // the range is asserted below
fn i64_from_f64(value: f64) -> i64 {
    assert!(
        value >= -(2f64.powi(63)) && value < 2f64.powi(63),
        "{OVERFLOW_MICROSECONDS}, got {value}"
    );
    value as i64
}

impl IntervalDsl for f64 {
    fn microseconds(self) -> PgInterval {
        i64_from_f64(self.round()).microseconds()
    }

    fn days(self) -> PgInterval {
        let fractional_days = (self.fract() * 86_400.0).seconds();
        PgInterval::from_days(i32_from_f64(self.trunc())) + fractional_days
    }

    fn months(self) -> PgInterval {
        let fractional_months = (self.fract() * 30.0).days();
        PgInterval::from_months(i32_from_f64(self.trunc())) + fractional_months
    }

    fn years(self) -> PgInterval {
        i32_from_f64((self * 12.0).round()).months()
    }
}

#[cfg(test)]
// those macros define nested function
// that's fine for this test code
#[allow(clippy::items_after_statements)]
mod tests {
    extern crate dotenvy;
    extern crate quickcheck;

    use self::quickcheck::quickcheck;

    use super::*;
    use crate::dsl::sql;
    use crate::prelude::*;
    use crate::test_helpers::*;
    use crate::{select, sql_types};

    /// Runs a builder, returning its panic message instead of unwinding.
    fn checked(f: impl Fn() -> PgInterval) -> Result<PgInterval, String> {
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(f)).map_err(|payload| {
            payload
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| payload.downcast_ref::<&str>().map(|s| (*s).to_owned()))
                .unwrap_or_default()
        })
    }

    #[diesel_test_helper::test]
    fn regression_interval_builders_report_overflow() {
        let cases: Vec<(&str, Box<dyn Fn() -> PgInterval>)> = vec![
            ("200000000i32.years()", Box::new(|| 200_000_000i32.years())),
            ("i32::MAX.years()", Box::new(|| i32::MAX.years())),
            ("i32::MAX.weeks()", Box::new(|| i32::MAX.weeks())),
            ("i64::MAX.years()", Box::new(|| i64::MAX.years())),
            ("i64::MAX.weeks()", Box::new(|| i64::MAX.weeks())),
            ("i64::MAX.hours()", Box::new(|| i64::MAX.hours())),
            ("i64::MAX.minutes()", Box::new(|| i64::MAX.minutes())),
            ("i64::MAX.seconds()", Box::new(|| i64::MAX.seconds())),
            (
                "i64::MAX.milliseconds()",
                Box::new(|| i64::MAX.milliseconds()),
            ),
            ("i64::MAX.days()", Box::new(|| i64::MAX.days())),
            ("i64::MAX.months()", Box::new(|| i64::MAX.months())),
            ("f64::MAX.years()", Box::new(|| f64::MAX.years())),
            ("f64::MAX.days()", Box::new(|| f64::MAX.days())),
            ("f64::MAX.months()", Box::new(|| f64::MAX.months())),
            (
                "f64::MAX.microseconds()",
                Box::new(|| f64::MAX.microseconds()),
            ),
            ("f64::NAN.days()", Box::new(|| f64::NAN.days())),
            (
                "f64::NAN.microseconds()",
                Box::new(|| f64::NAN.microseconds()),
            ),
            ("f64::INFINITY.days()", Box::new(|| f64::INFINITY.days())),
            ("1e300.days()", Box::new(|| 1e300f64.days())),
            ("-1e300.months()", Box::new(|| (-1e300f64).months())),
            (
                "i32::MAX.months() + i32::MAX.months()",
                Box::new(|| i32::MAX.months() + i32::MAX.months()),
            ),
            (
                "i64::MAX.microseconds() + 1.microseconds()",
                Box::new(|| i64::MAX.microseconds() + 1i32.microseconds()),
            ),
        ];
        let mut accepted = Vec::new();
        for (name, case) in cases {
            match checked(case) {
                Ok(interval) => accepted.push(format!(
                    "{name} returned months={} days={} us={}",
                    interval.months, interval.days, interval.microseconds
                )),
                Err(message) => assert!(
                    message.contains("Maximal supported"),
                    "{name} panicked with {message:?}"
                ),
            }
        }
        assert!(
            accepted.is_empty(),
            "{} unrepresentable intervals were accepted, first {:?}",
            accepted.len(),
            &accepted[..accepted.len().min(3)]
        );
    }

    #[diesel_test_helper::test]
    fn regression_interval_builders_do_not_wrap() {
        let mut state: u64 = 0x2545F4914F6CDD1D;
        let mut next = move || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        let mut wrong = Vec::new();

        // (name, microseconds per unit, days per unit, months per unit)
        let units: [(&str, i128, i128, i128); 9] = [
            ("microseconds", 1, 0, 0),
            ("milliseconds", 1_000, 0, 0),
            ("seconds", 1_000_000, 0, 0),
            ("minutes", 60_000_000, 0, 0),
            ("hours", 3_600_000_000, 0, 0),
            ("days", 0, 1, 0),
            ("weeks", 0, 7, 0),
            ("months", 0, 0, 1),
            ("years", 0, 0, 12),
        ];
        let build = |unit: &str, value: i64| -> Result<PgInterval, String> {
            match unit {
                "microseconds" => checked(move || value.microseconds()),
                "milliseconds" => checked(move || value.milliseconds()),
                "seconds" => checked(move || value.seconds()),
                "minutes" => checked(move || value.minutes()),
                "hours" => checked(move || value.hours()),
                "days" => checked(move || value.days()),
                "weeks" => checked(move || value.weeks()),
                "months" => checked(move || value.months()),
                "years" => checked(move || value.years()),
                _ => unreachable!(),
            }
        };

        let mut values = vec![
            0i64,
            1,
            -1,
            i64::MAX,
            i64::MIN,
            i64::from(i32::MAX),
            i64::from(i32::MIN),
            i64::from(i32::MAX) + 1,
            i64::from(i32::MIN) - 1,
            71_582_788,
            200_000_000,
        ];
        values.extend((0..512).map(|_| i64::from_ne_bytes(next().to_ne_bytes())));

        for (unit, us_per, days_per, months_per) in units {
            for value in &values {
                let wide = i128::from(*value);
                let expected_us = wide * us_per;
                let expected_days = wide * days_per;
                let expected_months = wide * months_per;
                let representable = i64::try_from(expected_us).is_ok()
                    && i32::try_from(expected_days).is_ok()
                    && i32::try_from(expected_months).is_ok();
                match (build(unit, *value), representable) {
                    (Ok(interval), true) => {
                        let got = (
                            i128::from(interval.microseconds),
                            i128::from(interval.days),
                            i128::from(interval.months),
                        );
                        if got != (expected_us, expected_days, expected_months) {
                            wrong.push(format!("{value}.{unit}() gave {got:?}"));
                        }
                    }
                    (Ok(interval), false) => wrong.push(format!(
                        "{value}.{unit}() gave months={} days={} us={} for an unrepresentable interval",
                        interval.months, interval.days, interval.microseconds
                    )),
                    (Err(message), true) => wrong.push(format!(
                        "{value}.{unit}() refused a representable interval with {message:?}"
                    )),
                    // diesel's own refusal, since an arithmetic overflow is silent in release
                    (Err(message), false) => {
                        if !message.contains("Maximal supported") {
                            wrong.push(format!("{value}.{unit}() panicked with {message:?}"));
                        }
                    }
                }
            }
        }
        assert!(
            wrong.is_empty(),
            "{} builders misbehaved, first {:?}",
            wrong.len(),
            &wrong[..wrong.len().min(3)]
        );
    }

    macro_rules! test_fn {
        ($tpe:ty, $test_name:ident, $units: ident, $max_range: expr) => {
            test_fn!($tpe, $test_name, $units, $max_range, 1, 0);
        };
        ($tpe:ty, $test_name:ident, $units:ident, $max_range: expr, $max_diff: expr) => {
            test_fn!($tpe, $test_name, $units, $max_range, $max_diff, 0);
        };
        ($tpe:ty, $test_name:ident, $units:ident, $max_range: expr, $max_diff: expr, $max_month_diff: expr) => {
            fn $test_name(val: $tpe) -> bool {
                if val > $max_range || val < (-1 as $tpe) * $max_range || (val as f64).is_nan() {
                    return true;
                }
                let conn = &mut pg_connection();
                let sql_str = format!(concat!("'{} ", stringify!($units), "'::interval"), val);
                let query = select(sql::<sql_types::Interval>(&sql_str));
                let value = val.$units();
                query
                    .get_result::<PgInterval>(conn)
                    .map(|res| {
                        (value.months - res.months).abs() <= $max_month_diff
                            && value.days == res.days
                            && (value.microseconds - res.microseconds).abs() <= $max_diff
                    })
                    .unwrap_or(false)
            }

            quickcheck($test_name as fn($tpe) -> bool);
        };
    }

    #[diesel_test_helper::test]
    fn intervals_match_pg_values_i32() {
        test_fn!(i32, test_microseconds, microseconds, i32::MAX);
        test_fn!(i32, test_milliseconds, milliseconds, i32::MAX);
        test_fn!(i32, test_seconds, seconds, i32::MAX);
        test_fn!(i32, test_minutes, minutes, i32::MAX);
        test_fn!(i32, test_hours, hours, i32::MAX);
        test_fn!(i32, test_days, days, i32::MAX);
        test_fn!(i32, test_weeks, weeks, i32::MAX / 7);
        test_fn!(i32, test_months, months, i32::MAX);
        test_fn!(i32, test_years, years, i32::MAX / 12);
    }

    #[diesel_test_helper::test]
    fn intervals_match_pg_values_i64() {
        // postgres does not really support intervals with more than i32::MAX microseconds
        // https://www.postgresql.org/message-id/20140126025049.GL9750@momjian.us
        test_fn!(i64, test_microseconds, microseconds, i32::MAX as i64);
        test_fn!(i64, test_milliseconds, milliseconds, i32::MAX as i64);
        test_fn!(i64, test_seconds, seconds, i32::MAX as i64);
        test_fn!(i64, test_minutes, minutes, i32::MAX as i64);
        test_fn!(i64, test_hours, hours, i32::MAX as i64);
        test_fn!(i64, test_days, days, i32::MAX as i64);
        test_fn!(i64, test_weeks, weeks, (i32::MAX / 7) as i64);
        test_fn!(i64, test_months, months, i32::MAX as i64);
        test_fn!(i64, test_years, years, (i32::MAX / 12) as i64);
    }

    #[diesel_test_helper::test]
    fn intervals_match_pg_values_f64() {
        const MAX_DIFF: i64 = 1_000_000;
        // postgres does not really support intervals with more than i32::MAX microseconds
        // https://www.postgresql.org/message-id/20140126025049.GL9750@momjian.us
        test_fn!(
            f64,
            test_microseconds,
            microseconds,
            i32::MAX as f64,
            MAX_DIFF
        );
        test_fn!(
            f64,
            test_milliseconds,
            milliseconds,
            i32::MAX as f64,
            MAX_DIFF
        );
        test_fn!(f64, test_seconds, seconds, i32::MAX as f64, MAX_DIFF);
        test_fn!(f64, test_minutes, minutes, i32::MAX as f64, MAX_DIFF);
        test_fn!(f64, test_hours, hours, i32::MAX as f64, MAX_DIFF);
        test_fn!(f64, test_days, days, i32::MAX as f64, MAX_DIFF);
        test_fn!(f64, test_weeks, weeks, (i32::MAX / 7) as f64, MAX_DIFF);
        test_fn!(f64, test_months, months, i32::MAX as f64, MAX_DIFF);
        // different postgres versions seem to round intervals with years differently
        // -1681.9781874756495 years is reported as -20183 months for postgres 14
        // and as -20184 months for postgres 16
        test_fn!(f64, test_years, years, (i32::MAX / 12) as f64, MAX_DIFF, 1);
    }
}
