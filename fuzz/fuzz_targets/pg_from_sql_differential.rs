#![no_main]
//! Diesel and `postgres-types` must read the same postgres wire bytes as the same value, and
//! each must read what the other writes.

use arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;

#[derive(Arbitrary, Debug)]
struct Input<'a> {
    selector: u8,
    bytes: &'a [u8],
}

fuzz_target!(|input: Input<'_>| {
    if let Err(violation) = diesel_fuzz::pg_differential::check_case(input.selector, input.bytes) {
        panic!("{violation}");
    }
});
