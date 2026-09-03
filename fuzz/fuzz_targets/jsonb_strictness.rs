#![no_main]
//! Every blob sqlite accepts and diesel refuses must fall in a known class.

use libfuzzer_sys::fuzz_target;

fuzz_target!(|blob: &[u8]| {
    diesel_fuzz::sqlite::with_conn(|conn| {
        diesel_fuzz::assert_no_violation(diesel_fuzz::jsonb::check_strictness(conn, blob));
    });
});
