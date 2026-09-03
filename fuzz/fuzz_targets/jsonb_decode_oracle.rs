#![no_main]
//! Diesel and sqlite must agree on what a blob means.

use libfuzzer_sys::fuzz_target;

fuzz_target!(|blob: &[u8]| {
    diesel_fuzz::sqlite::with_conn(|conn| {
        diesel_fuzz::assert_no_violation(diesel_fuzz::jsonb::check_decode(conn, blob));
    });
});
