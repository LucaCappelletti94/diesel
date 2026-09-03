//! Fuzz harnesses for diesel's deserialization code.

pub mod datetime;
pub mod differential;
pub mod jsonb;
pub mod mysql;
pub mod pg;
pub mod sqlite;

/// Panics with the finding, so libFuzzer keeps the input that produced it.
pub fn assert_no_violation<V: std::fmt::Display>(violation: Option<V>) {
    if let Some(violation) = violation {
        panic!("{violation}");
    }
}
