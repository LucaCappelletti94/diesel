//! Grammar-built blobs, so the container paths byte mutation rarely finds stay
//! reachable.

use super::format::{ARRAY, FLOAT, Header, INT, OBJECT, TEXT, TEXTJ, TEXTRAW, encode_header};
use arbitrary::{Arbitrary, Result, Unstructured};

const MAX_DEPTH: u32 = 8;
const MAX_ITEMS: usize = 8;

/// A grammar-built blob, with headers sometimes perturbed.
#[derive(Debug)]
pub struct ArbitraryJsonb(pub Vec<u8>);

impl<'a> Arbitrary<'a> for ArbitraryJsonb {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        element(u, 0).map(ArbitraryJsonb)
    }
}

fn element(u: &mut Unstructured<'_>, depth: u32) -> Result<Vec<u8>> {
    let leaf_only = depth >= MAX_DEPTH || u.is_empty();
    let tag = if leaf_only {
        u.int_in_range(0x00u8..=0x0A)?
    } else {
        u.int_in_range(0x00u8..=0x0F)?
    };
    let payload = match tag {
        // both signs of the range, since the reader parses the payload as i64
        INT if bool::arbitrary(u)? => i64::arbitrary(u)?.to_string().into_bytes(),
        INT => u64::arbitrary(u)?.to_string().into_bytes(),
        FLOAT => f64::arbitrary(u)?.to_string().into_bytes(),
        TEXT | TEXTJ | TEXTRAW => Vec::<u8>::arbitrary(u)?,
        ARRAY => {
            let mut payload = Vec::new();
            for _ in 0..u.arbitrary_len::<u8>()?.min(MAX_ITEMS) {
                payload.extend(element(u, depth + 1)?);
            }
            payload
        }
        OBJECT => {
            let mut payload = Vec::new();
            for _ in 0..u.arbitrary_len::<u8>()?.min(MAX_ITEMS) {
                payload.extend(text(u)?);
                payload.extend(element(u, depth + 1)?);
            }
            payload
        }
        _ => Vec::<u8>::arbitrary(u)?,
    };
    with_header(u, tag, payload)
}

fn text(u: &mut Unstructured<'_>) -> Result<Vec<u8>> {
    let payload = Vec::<u8>::arbitrary(u)?;
    with_header(u, TEXT, payload)
}

/// The header is deliberately allowed to be wider than the payload needs, or
/// to declare the wrong size.
fn with_header(u: &mut Unstructured<'_>, tag: u8, payload: Vec<u8>) -> Result<Vec<u8>> {
    let declared = declared_size(u, payload.len())?;
    let header = match u.int_in_range(0u8..=4)? {
        0 => Header::narrowest(declared),
        1 => Header::Byte,
        2 => Header::Word,
        3 => Header::Long,
        _ => Header::Quad,
    };
    let mut blob = encode_header(header, tag, declared);
    blob.extend(payload);
    Ok(blob)
}

/// Usually honest, so deep structures stay reachable.
fn declared_size(u: &mut Unstructured<'_>, actual: usize) -> Result<usize> {
    match u.int_in_range(0u8..=15)? {
        0 => Ok(actual.saturating_add(1)),
        1 => Ok(actual.saturating_sub(1)),
        2 => Ok(usize::from(u16::arbitrary(u)?)),
        _ => Ok(actual),
    }
}
