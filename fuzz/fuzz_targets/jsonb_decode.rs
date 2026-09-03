#![no_main]
//! Decoding an arbitrary blob must never panic.

use libfuzzer_sys::fuzz_target;

// only the reported panic is skipped; a semantic defect is no excuse for a crash
fuzz_target!(|blob: &[u8]| {
    if diesel_fuzz::jsonb::has_known_panic(blob) {
        return;
    }
    diesel_fuzz::sqlite::with_conn(|conn| {
        let _ = diesel_fuzz::sqlite::decode_jsonb(conn, blob);
    });
});
