#![no_main]
//! Grammar-built blobs reach the container paths byte mutation rarely finds.

use diesel_fuzz::jsonb::ArbitraryJsonb;
use libfuzzer_sys::fuzz_target;

fuzz_target!(|input: ArbitraryJsonb| {
    let ArbitraryJsonb(blob) = input;
    diesel_fuzz::sqlite::with_conn(|conn| {
        diesel_fuzz::assert_no_violation(diesel_fuzz::jsonb::check_decode(conn, &blob));
        diesel_fuzz::assert_no_violation(diesel_fuzz::jsonb::check_strictness(conn, &blob));
    });
});
