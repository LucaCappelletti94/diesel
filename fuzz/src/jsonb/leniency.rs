//! Naming a divergence from sqlite, and proving the name causes it.

use super::format::{
    FALSE, FLOAT, FLOAT5, Header, INT, INT5, NULL, Node, Payload, TEXT, TEXT5, TEXTJ, TEXTRAW,
    TRUE, emit, parse,
};

/// A known, expected divergence from sqlite.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Leniency {
    /// Constants are read without checking for a bare one-byte header.
    ConstantPayload,
    /// TEXT and TEXTRAW share one reader.
    TextEscaping,
    /// `serde_json` tolerates whitespace around a numeric payload.
    NumericFormat,
    /// JSON5 element types, refused on purpose.
    Json5Type,
    /// A number `serde_json` cannot hold.
    NumberOutOfRange,
    /// A text payload `serde_json::Value` cannot hold.
    NonUtf8Text,
    /// An escape `serde_json` refuses, such as a lone surrogate.
    EscapeNotRepresentable,
}

impl std::fmt::Display for Leniency {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let name = match self {
            Self::ConstantPayload => "ConstantPayload",
            Self::TextEscaping => "TextEscaping",
            Self::NumericFormat => "NumericFormat",
            Self::Json5Type => "Json5Type",
            Self::NumberOutOfRange => "NumberOutOfRange",
            Self::NonUtf8Text => "NonUtf8Text",
            Self::EscapeNotRepresentable => "EscapeNotRepresentable",
        };
        f.write_str(name)
    }
}

/// The blob with every known feature rewritten away, and every class removed
/// on the way, first occurrence first; whether that removal explains a
/// divergence is `properties`' to say.
pub fn repair(blob: &[u8]) -> Option<(Vec<u8>, Vec<Leniency>)> {
    let mut node = parse(blob)?;
    let mut classes = Vec::new();
    normalise(&mut node, &mut classes);
    (!classes.is_empty()).then(|| (emit(&node), classes))
}

/// Rewrites every known feature away, naming each one it removed.
fn normalise(node: &mut Node, classes: &mut Vec<Leniency>) {
    let Node {
        tag,
        header,
        payload,
    } = node;
    let bytes = match payload {
        Payload::Items(items) => {
            for item in items {
                normalise(item, classes);
            }
            return;
        }
        Payload::Leaf(bytes) => bytes,
    };
    let Some(class) = leaf_class(*tag, *header, bytes) else {
        return;
    };
    if !classes.contains(&class) {
        classes.push(class);
    }
    match class {
        Leniency::ConstantPayload => {
            *header = Header::Inline;
            bytes.clear();
        }
        Leniency::TextEscaping => *tag = TEXTRAW,
        Leniency::NonUtf8Text | Leniency::EscapeNotRepresentable => {
            *tag = TEXT;
            *bytes = b"a".to_vec();
        }
        Leniency::Json5Type => match *tag {
            INT5 => {
                *tag = INT;
                *bytes = b"1".to_vec();
            }
            FLOAT5 => {
                *tag = FLOAT;
                *bytes = b"1.0".to_vec();
            }
            _ => {
                *tag = TEXT;
                *bytes = b"a".to_vec();
            }
        },
        Leniency::NumericFormat | Leniency::NumberOutOfRange => {
            *bytes = if *tag == INT {
                b"1".to_vec()
            } else {
                b"1.0".to_vec()
            };
        }
    }
}

fn leaf_class(tag: u8, header: Header, payload: &[u8]) -> Option<Leniency> {
    match tag {
        NULL | TRUE | FALSE if !payload.is_empty() || header != Header::Inline => {
            Some(Leniency::ConstantPayload)
        }
        INT5 | FLOAT5 | TEXT5 => Some(Leniency::Json5Type),
        TEXT | TEXTJ | TEXTRAW if str::from_utf8(payload).is_err() => Some(Leniency::NonUtf8Text),
        TEXTJ if !holds_as_string(payload) => Some(Leniency::EscapeNotRepresentable),
        TEXT if payload.iter().any(needs_escaping) => Some(Leniency::TextEscaping),
        INT | FLOAT if !well_formed_number(payload, tag) => Some(Leniency::NumericFormat),
        INT if !fits_i64(payload) => Some(Leniency::NumberOutOfRange),
        FLOAT if !holds_as_number(payload) => Some(Leniency::NumberOutOfRange),
        _ => None,
    }
}

/// Mirrors diesel's own check.
fn fits_i64(payload: &[u8]) -> bool {
    number(payload).is_some_and(|value| value.is_i64())
}

/// A float payload sqlite renders but `serde_json` cannot hold, such as `1e999`.
fn holds_as_number(payload: &[u8]) -> bool {
    number(payload).is_some()
}

/// A TEXTJ payload sqlite keeps but `serde_json` refuses, such as `\ud83d`
/// without its pair.
fn holds_as_string(payload: &[u8]) -> bool {
    str::from_utf8(payload)
        .is_ok_and(|text| serde_json::from_str::<String>(&format!("\"{text}\"")).is_ok())
}

fn needs_escaping(byte: &u8) -> bool {
    matches!(byte, 0x00..=0x1F | b'"' | b'\\')
}

fn number(payload: &[u8]) -> Option<serde_json::Value> {
    let text = str::from_utf8(payload).ok()?;
    let value: serde_json::Value = serde_json::from_str(text).ok()?;
    value.is_number().then_some(value)
}

/// The RFC 8259 number grammar, read from the text alone so a payload sqlite
/// spells differently is a format class and not a range one; an INT carries no
/// fraction or exponent, a FLOAT carries at least one.
fn well_formed_number(payload: &[u8], tag: u8) -> bool {
    let Ok(text) = str::from_utf8(payload) else {
        return false;
    };
    let digits = text.strip_prefix('-').unwrap_or(text);
    let (integer, fraction) = match digits.split_once(['e', 'E']) {
        Some((mantissa, exponent)) if tag == FLOAT => {
            let exponent = exponent.strip_prefix(['+', '-']).unwrap_or(exponent);
            if exponent.is_empty() || !exponent.bytes().all(|byte| byte.is_ascii_digit()) {
                return false;
            }
            (mantissa, true)
        }
        Some(_) => return false,
        None => (digits, false),
    };
    let (whole, decimals) = match integer.split_once('.') {
        Some((whole, decimals)) => {
            if tag == INT
                || decimals.is_empty()
                || !decimals.bytes().all(|byte| byte.is_ascii_digit())
            {
                return false;
            }
            (whole, true)
        }
        None => (integer, false),
    };
    if tag == FLOAT && !fraction && !decimals {
        return false;
    }
    !whole.is_empty()
        && whole.bytes().all(|byte| byte.is_ascii_digit())
        && (whole == "0" || !whole.starts_with('0'))
}
