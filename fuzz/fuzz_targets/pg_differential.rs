#![no_main]
//! Cross-library agreement properties for postgres types must hold.

use arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use std::num::NonZeroU32;

#[derive(Arbitrary, Debug)]
struct Input<'a> {
    selector: u8,
    oid: u32,
    bytes: &'a [u8],
}

fuzz_target!(|input: Input<'_>| {
    let oid = NonZeroU32::new(input.oid).unwrap_or(NonZeroU32::MIN);
    diesel_fuzz::assert_no_violation(diesel_fuzz::pg::differential(
        input.selector,
        oid,
        input.bytes,
    ));
});
