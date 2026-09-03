#![no_main]
//! The chrono and time text parsers must not disagree on a date or a time.

use libfuzzer_sys::fuzz_target;

fuzz_target!(|text: &str| {
    diesel_fuzz::sqlite::with_conn(|conn| {
        diesel_fuzz::assert_no_violation(diesel_fuzz::datetime::check_text(conn, text));
    });
});
