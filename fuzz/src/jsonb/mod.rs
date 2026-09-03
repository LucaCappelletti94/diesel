//! Sqlite JSONB properties, checked against sqlite itself.

mod arbitrary;
mod format;
mod leniency;
mod properties;

pub use arbitrary::ArbitraryJsonb;
pub use format::{
    ARRAY, Element, FALSE, FLOAT, FLOAT5, Header, INT, INT5, NULL, OBJECT, TEXT, TEXT5, TEXTJ,
    TEXTRAW, TRUE, encode_header, has_known_panic, has_known_reader_defect, walk,
};
pub use leniency::{Leniency, repair};
pub use properties::{
    Violation, agree, check_decode, check_encode, check_encode_bytes, check_strictness,
    explains_divergence, json_eq, known_writer_defect, rendered_eq,
};
