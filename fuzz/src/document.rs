//! A json document generated from entropy rather than parsed from text.
//!
//! Parsing the input with `serde_json` would hide a writer defect: the reader
//! parses with `serde_json` too, so both sides make the same rounding error and
//! the round trip agrees on a value neither spells correctly.

use arbitrary::Arbitrary;
use serde_json::{Map, Number, Value};

#[derive(Arbitrary, Debug)]
pub enum Document {
    Null,
    Bool(bool),
    Signed(i64),
    Unsigned(u64),
    Float(f64),
    Text(String),
    Array(Vec<Document>),
    Object(Vec<(String, Document)>),
}

impl From<&Document> for Value {
    fn from(document: &Document) -> Self {
        match document {
            Document::Null => Value::Null,
            Document::Bool(value) => Value::Bool(*value),
            Document::Signed(value) => Value::Number(Number::from(*value)),
            Document::Unsigned(value) => Value::Number(Number::from(*value)),
            // json holds no infinity and no nan, and `from_f64` says so
            Document::Float(value) => Number::from_f64(*value).map_or(Value::Null, Value::Number),
            Document::Text(value) => Value::String(value.clone()),
            Document::Array(items) => Value::Array(items.iter().map(Value::from).collect()),
            Document::Object(entries) => Value::Object(
                entries
                    .iter()
                    .map(|(key, value)| (key.clone(), Value::from(value)))
                    .collect::<Map<_, _>>(),
            ),
        }
    }
}
