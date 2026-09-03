#![no_main]
//! What diesel writes, sqlite and diesel must both read back unchanged.

use libfuzzer_sys::fuzz_target;

// the document is parsed from the input, so a seed means the json it spells
fuzz_target!(|data: &[u8]| {
    diesel_fuzz::sqlite::with_conn(|conn| {
        diesel_fuzz::assert_no_violation(diesel_fuzz::jsonb::check_encode_bytes(conn, data));
    });
});
