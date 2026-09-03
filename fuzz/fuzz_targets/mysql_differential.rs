#![no_main]
//! chrono and `time` must agree when both decode the same MySQL date/time bytes.

use arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;

#[derive(Arbitrary, Debug)]
struct Input<'a> {
    selector: u8,
    type_selector: u8,
    bytes: &'a [u8],
}

fuzz_target!(|input: Input<'_>| {
    diesel_fuzz::assert_no_violation(diesel_fuzz::mysql::differential(
        input.selector,
        input.type_selector,
        input.bytes,
    ));
});
