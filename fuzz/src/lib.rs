//! Fuzz harnesses for diesel's deserialization code, reaching diesel only
//! through its public API.

pub mod document;
pub mod mysql;
pub mod pg;
pub mod sqlite;
