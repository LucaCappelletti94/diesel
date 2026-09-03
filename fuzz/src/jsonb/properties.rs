//! What must hold between diesel and sqlite for one blob.

use super::format::has_known_reader_defect;
use super::leniency::{Leniency, repair};
use crate::sqlite::{Oracle, decode_jsonb, encode_jsonb, jsonb_strictly_valid, oracle};
use diesel::SqliteConnection;

/// Whether diesel and sqlite read the same value from a blob.
pub fn agree(conn: &mut SqliteConnection, blob: &[u8]) -> bool {
    if !jsonb_strictly_valid(conn, blob) {
        return false;
    }
    let Ok(diesel) = decode_jsonb(conn, blob) else {
        return false;
    };
    let Oracle::Value(sqlite) = oracle(conn, blob) else {
        return false;
    };
    rendered_eq(&diesel, &sqlite)
}

/// The known features that cause a divergence, proven by removing them: with
/// every known feature rewritten away, diesel and sqlite must read the same
/// value, so an unrelated mismatch cannot hide behind a known one. Every class
/// removed is named, since one alone need not account for the divergence.
pub fn explains_divergence(conn: &mut SqliteConnection, blob: &[u8]) -> Option<Vec<Leniency>> {
    let (repaired, classes) = repair(blob)?;
    agree(conn, &repaired).then_some(classes)
}

/// A jsonb finding; the variant is its class.
#[derive(Debug, thiserror::Error)]
pub enum Violation {
    #[error("diesel decoded {value} from a blob sqlite rejects")]
    AcceptsInvalid { value: serde_json::Value },
    #[error("diesel decoded {diesel}, sqlite decoded {sqlite}")]
    Mismatch {
        diesel: serde_json::Value,
        sqlite: serde_json::Value,
    },
    #[error("diesel rejected a blob sqlite reads as {sqlite}: {error}")]
    RejectsValid { sqlite: String, error: String },
    #[error("diesel refused to encode {value}: {error}")]
    WriteFailed {
        value: serde_json::Value,
        error: String,
    },
    #[error("sqlite rejects the blob diesel wrote for {value}: {blob:02X?}")]
    WritesInvalid {
        value: serde_json::Value,
        blob: Vec<u8>,
    },
    #[error("diesel wrote {value} but sqlite reads {sqlite} back")]
    ForeignRoundTrip {
        value: serde_json::Value,
        sqlite: serde_json::Value,
    },
    #[error("diesel wrote {value} but sqlite renders {rendering}, which is no json value")]
    ForeignRendering {
        value: serde_json::Value,
        rendering: String,
    },
    #[error("diesel cannot read back the blob it wrote for {value}: {error}")]
    SelfRoundTrip {
        value: serde_json::Value,
        error: String,
    },
    #[error("sqlite calls the blob valid but json() refused it: {reason}")]
    OracleFailed { reason: String },
}

/// Diesel and sqlite must agree, and an accept-invalid must have a class.
pub fn check_decode(conn: &mut SqliteConnection, blob: &[u8]) -> Option<Violation> {
    if has_known_reader_defect(blob) {
        return None;
    }
    let decoded = decode_jsonb(conn, blob).ok()?;
    match oracle(conn, blob) {
        // a mismatch is a finding unless a known feature causes it, the same
        // rule an accept-invalid gets
        Oracle::Value(sqlite) => (!rendered_eq(&decoded, &sqlite)
            && explains_divergence(conn, blob).is_none())
        .then_some(Violation::Mismatch {
            diesel: decoded,
            sqlite,
        }),
        // sqlite reads the blob, so diesel accepting it is no divergence; the
        // two readings cannot be compared as `serde_json` values
        Oracle::Unrepresentable(_) | Oracle::NonUtf8(_) => None,
        Oracle::Failed(reason) if jsonb_strictly_valid(conn, blob) => {
            Some(Violation::OracleFailed { reason })
        }
        Oracle::Failed(_) => explains_divergence(conn, blob)
            .is_none()
            .then_some(Violation::AcceptsInvalid { value: decoded }),
    }
}

/// A reject-valid must have a class.
pub fn check_strictness(conn: &mut SqliteConnection, blob: &[u8]) -> Option<Violation> {
    if has_known_reader_defect(blob) || !jsonb_strictly_valid(conn, blob) {
        return None;
    }
    let error = decode_jsonb(conn, blob).err()?;
    let sqlite = match oracle(conn, blob) {
        Oracle::Value(value) => value.to_string(),
        Oracle::Unrepresentable(text) => text,
        Oracle::NonUtf8(rendering) => format!("{rendering:02X?}"),
        Oracle::Failed(reason) => return Some(Violation::OracleFailed { reason }),
    };
    explains_divergence(conn, blob)
        .is_none()
        .then_some(Violation::RejectsValid {
            sqlite,
            error: error.to_string(),
        })
}

/// Checks the document `data` spells; a payload that is not json is skipped.
pub fn check_encode_bytes(conn: &mut SqliteConnection, data: &[u8]) -> Option<Violation> {
    check_encode(conn, &serde_json::from_slice(data).ok()?)
}

/// The value shapes the writer is reported to mangle: a float whose `Display`
/// carries no fraction or exponent, an unsigned integer past `i64::MAX`, and a
/// string needing an escape TEXT cannot hold. Delete with the fix.
pub fn known_writer_defect(value: &serde_json::Value) -> bool {
    use serde_json::Value::{Array, Number, Object, String};
    match value {
        Number(number) => match (number.as_i64(), number.as_u64(), number.as_f64()) {
            (None, Some(_), _) => true,
            (None, None, Some(float)) => {
                !float.to_string().contains(['.', 'e', 'E']) || reparses_differently(float)
            }
            _ => false,
        },
        String(text) => needs_raw_text(text),
        Array(items) => items.iter().any(known_writer_defect),
        Object(map) => {
            map.keys().any(|key| needs_raw_text(key)) || map.values().any(known_writer_defect)
        }
        _ => false,
    }
}

/// `serde_json`'s float parser is not correctly rounded, so a double whose own
/// `Display` re-parses to a different one cannot survive the writer's text.
fn reparses_differently(float: f64) -> bool {
    serde_json::from_str::<f64>(&float.to_string())
        .is_ok_and(|back| back.to_bits() != float.to_bits())
}

fn needs_raw_text(text: &str) -> bool {
    text.contains(['"', '\\'])
}

/// Diesel's own blob must be valid JSONB and mean what it wrote.
pub fn check_encode(conn: &mut SqliteConnection, value: &serde_json::Value) -> Option<Violation> {
    if known_writer_defect(value) {
        return None;
    }
    let blob = match encode_jsonb(conn, value) {
        Ok(blob) => blob,
        Err(error) => {
            return Some(Violation::WriteFailed {
                value: value.clone(),
                error: error.to_string(),
            });
        }
    };
    if !jsonb_strictly_valid(conn, &blob) {
        return Some(Violation::WritesInvalid {
            value: value.clone(),
            blob,
        });
    }
    let sqlite = match oracle(conn, &blob) {
        Oracle::Value(sqlite) => sqlite,
        // diesel wrote a document, so sqlite must read one back
        Oracle::Unrepresentable(rendering) => {
            return Some(Violation::ForeignRendering {
                value: value.clone(),
                rendering,
            });
        }
        Oracle::NonUtf8(rendering) => {
            return Some(Violation::ForeignRendering {
                value: value.clone(),
                rendering: format!("{rendering:02X?}"),
            });
        }
        Oracle::Failed(reason) => return Some(Violation::OracleFailed { reason }),
    };
    if !rendered_eq(value, &sqlite) {
        return Some(Violation::ForeignRoundTrip {
            value: value.clone(),
            sqlite,
        });
    }
    match decode_jsonb(conn, &blob) {
        Ok(back) if json_eq(&back, value) => None,
        Ok(back) => Some(Violation::Mismatch {
            diesel: back,
            sqlite,
        }),
        Err(error) => Some(Violation::SelfRoundTrip {
            value: value.clone(),
            error: error.to_string(),
        }),
    }
}

/// Numbers compare exactly, so a float only equals an integer it represents
/// without rounding.
pub fn json_eq(left: &serde_json::Value, right: &serde_json::Value) -> bool {
    compare_values(left, right, |left, right| left == right)
}

/// The same, at the precision sqlite's `json()` renders a double with: fifteen
/// significant digits, so asking its rendering for more is asking sqlite, not
/// diesel.
pub fn rendered_eq(diesel: &serde_json::Value, sqlite: &serde_json::Value) -> bool {
    compare_values(diesel, sqlite, |left, right| {
        format!("{left:.14e}") == format!("{right:.14e}")
    })
}

fn compare_values(
    left: &serde_json::Value,
    right: &serde_json::Value,
    floats: fn(f64, f64) -> bool,
) -> bool {
    use serde_json::Value::{Array, Number, Object};
    match (left, right) {
        (Number(left), Number(right)) => match (exact_integer(left), exact_integer(right)) {
            (Some(left), Some(right)) => left == right,
            _ => match (left.as_f64(), right.as_f64()) {
                (Some(left), Some(right)) => floats(left, right),
                _ => left == right,
            },
        },
        (Array(left), Array(right)) => {
            left.len() == right.len()
                && left
                    .iter()
                    .zip(right)
                    .all(|(left, right)| compare_values(left, right, floats))
        }
        (Object(left), Object(right)) => {
            left.len() == right.len()
                && left.iter().all(|(key, value)| {
                    right
                        .get(key)
                        .is_some_and(|other| compare_values(value, other, floats))
                })
        }
        _ => left == right,
    }
}

/// The integer a number denotes, whichever way `serde_json` stored it.
fn exact_integer(number: &serde_json::Number) -> Option<i128> {
    if let Some(signed) = number.as_i64() {
        return Some(i128::from(signed));
    }
    if let Some(unsigned) = number.as_u64() {
        return Some(i128::from(unsigned));
    }
    let float = number.as_f64()?;
    // i128 has no TryFrom<f64>, so bound the value before truncating
    (float.fract() == 0.0 && float.abs() < 2.0_f64.powi(127)).then_some(float as i128)
}
