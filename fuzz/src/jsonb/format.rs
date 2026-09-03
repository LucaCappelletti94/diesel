//! Sqlite's JSONB wire format: tags, headers, traversal and a repairable tree.

pub const NULL: u8 = 0x00;
pub const TRUE: u8 = 0x01;
pub const FALSE: u8 = 0x02;
pub const INT: u8 = 0x03;
pub const INT5: u8 = 0x04;
pub const FLOAT: u8 = 0x05;
pub const FLOAT5: u8 = 0x06;
pub const TEXT: u8 = 0x07;
pub const TEXTJ: u8 = 0x08;
pub const TEXT5: u8 = 0x09;
pub const TEXTRAW: u8 = 0x0A;
pub const ARRAY: u8 = 0x0B;
pub const OBJECT: u8 = 0x0C;

/// How wide a header writes its payload size; the format allows a wider class
/// than a payload needs, and a generator or a repair must be able to keep one.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Header {
    /// The size in the high nibble, for a payload under twelve bytes.
    Inline,
    Byte,
    Word,
    Long,
    Quad,
}

impl Header {
    /// The class a size of `bytes` fits in most narrowly.
    pub fn narrowest(bytes: usize) -> Self {
        match bytes {
            0..=0x0B => Self::Inline,
            size if size <= usize::from(u8::MAX) => Self::Byte,
            size if size <= usize::from(u16::MAX) => Self::Word,
            size if u32::try_from(size).is_ok() => Self::Long,
            _ => Self::Quad,
        }
    }

    /// The class a header of this many bytes uses.
    pub fn of_width(bytes: usize) -> Option<Self> {
        match bytes {
            1 => Some(Self::Inline),
            2 => Some(Self::Byte),
            3 => Some(Self::Word),
            5 => Some(Self::Long),
            9 => Some(Self::Quad),
            _ => None,
        }
    }

    /// The largest payload this class can declare.
    pub fn capacity(self) -> usize {
        match self {
            Self::Inline => 0x0B,
            Self::Byte => usize::from(u8::MAX),
            Self::Word => usize::from(u16::MAX),
            Self::Long => usize::try_from(u32::MAX).unwrap_or(usize::MAX),
            Self::Quad => usize::MAX,
        }
    }
}

/// Writes `tag` and `size` in the given class, widening only when the class
/// cannot hold the size.
pub fn encode_header(header: Header, tag: u8, size: usize) -> Vec<u8> {
    let header = if size <= header.capacity() {
        header
    } else {
        Header::narrowest(size)
    };
    match header {
        Header::Inline => vec![(u8::try_from(size).expect("under twelve") << 4) | tag],
        Header::Byte => vec![(0x0C << 4) | tag, u8::try_from(size).expect("under 256")],
        Header::Word => {
            let mut bytes = vec![(0x0D << 4) | tag];
            bytes.extend(u16::try_from(size).expect("under 65536").to_be_bytes());
            bytes
        }
        Header::Long => {
            let mut bytes = vec![(0x0E << 4) | tag];
            bytes.extend(u32::try_from(size).expect("under 4 GiB").to_be_bytes());
            bytes
        }
        Header::Quad => {
            let mut bytes = vec![(0x0F << 4) | tag];
            bytes.extend(u64::try_from(size).expect("a 64 bit size").to_be_bytes());
            bytes
        }
    }
}

#[derive(Debug)]
pub struct Element<'a> {
    pub tag: u8,
    pub declared_size: usize,
    pub header_size: usize,
    /// Where this element's header starts in the blob `walk` was given.
    pub offset: usize,
    pub payload: &'a [u8],
}

/// Flattens a blob into its elements, stopping at the first byte range the
/// format cannot explain; only used to name a divergence.
pub fn walk(blob: &[u8]) -> Vec<Element<'_>> {
    let mut elements = Vec::new();
    let mut stack = Vec::new();
    stack.push(0..blob.len());
    while let Some(range) = stack.pop() {
        let mut start = range.start;
        while start < range.end {
            let Some((element, consumed)) = split_element(&blob[start..range.end]) else {
                return elements;
            };
            let payload_start = start + element.header_size;
            let container = matches!(element.tag, ARRAY | OBJECT);
            elements.push(Element {
                offset: start,
                ..element
            });
            if container {
                stack.push(start + consumed..range.end);
                stack.push(payload_start..start + consumed);
                break;
            }
            start += consumed;
        }
    }
    elements
}

/// The element at the front of `blob`, and the bytes it spans.
pub fn split_element(blob: &[u8]) -> Option<(Element<'_>, usize)> {
    let first = *blob.first()?;
    let tag = first & 0x0F;
    let (declared_size, header): (usize, usize) = match first >> 4 {
        class @ 0x00..=0x0B => (usize::from(class), 1),
        0x0C => (usize::from(*blob.get(1)?), 2),
        0x0D => (
            usize::from(u16::from_be_bytes([*blob.get(1)?, *blob.get(2)?])),
            3,
        ),
        0x0E => (
            usize::try_from(u32::from_be_bytes([
                *blob.get(1)?,
                *blob.get(2)?,
                *blob.get(3)?,
                *blob.get(4)?,
            ]))
            .ok()?,
            5,
        ),
        _ => (
            usize::try_from(u64::from_be_bytes([
                *blob.get(1)?,
                *blob.get(2)?,
                *blob.get(3)?,
                *blob.get(4)?,
                *blob.get(5)?,
                *blob.get(6)?,
                *blob.get(7)?,
                *blob.get(8)?,
            ]))
            .ok()?,
            9,
        ),
    };
    let end = header.checked_add(declared_size)?;
    let payload = blob.get(header..end)?;
    Some((
        Element {
            tag,
            declared_size,
            header_size: header,
            offset: 0,
            payload,
        },
        end,
    ))
}

/// A strictly parsed element, holding its own header class so a repair leaves
/// every untouched byte as it was.
#[derive(Debug)]
pub struct Node {
    pub tag: u8,
    pub header: Header,
    pub payload: Payload,
}

#[derive(Debug)]
pub enum Payload {
    Leaf(Vec<u8>),
    Items(Vec<Node>),
}

/// Parses `blob` and its children exactly; slack, overrun or an odd object all
/// fail, since a repair must not paper over the structure.
pub fn parse(blob: &[u8]) -> Option<Node> {
    let (element, consumed) = split_element(blob)?;
    if consumed != blob.len() {
        return None;
    }
    let header = Header::of_width(element.header_size)?;
    if matches!(element.tag, ARRAY | OBJECT) {
        let mut items = Vec::new();
        let mut cursor = element.payload;
        while !cursor.is_empty() {
            let (_, consumed) = split_element(cursor)?;
            items.push(parse(cursor.get(..consumed)?)?);
            cursor = &cursor[consumed..];
        }
        if element.tag == OBJECT && items.len() % 2 != 0 {
            return None;
        }
        return Some(Node {
            tag: element.tag,
            header,
            payload: Payload::Items(items),
        });
    }
    Some(Node {
        tag: element.tag,
        header,
        payload: Payload::Leaf(element.payload.to_vec()),
    })
}

/// Serialises a node, keeping each header class the parse found.
pub fn emit(node: &Node) -> Vec<u8> {
    let payload = match &node.payload {
        Payload::Leaf(bytes) => bytes.clone(),
        Payload::Items(items) => items.iter().flat_map(emit).collect(),
    };
    let mut blob = encode_header(node.header, node.tag, payload.len());
    blob.extend(payload);
    blob
}

/// The reported header-arithmetic panic: a declared size with no room for its
/// own header. Read only where a header starts, and a child whose size cannot
/// be split still has a header the reader reaches.
pub fn has_known_panic(blob: &[u8]) -> bool {
    let mut ranges = Vec::new();
    ranges.push(0..blob.len());
    while let Some(range) = ranges.pop() {
        let mut start = range.start;
        while start < range.end {
            let element = &blob[start..range.end];
            if overflowing_header(element) {
                return true;
            }
            let Some((element, consumed)) = split_element(element) else {
                break;
            };
            if matches!(element.tag, ARRAY | OBJECT) {
                ranges.push(start + element.header_size..start + consumed);
            }
            start += consumed;
        }
    }
    false
}

fn overflowing_header(blob: &[u8]) -> bool {
    blob.first().is_some_and(|first| first >> 4 == 0x0F)
        && blob.len() >= 9
        && u64::from_be_bytes(blob[1..9].try_into().expect("nine bytes")) > u64::MAX - 9
}

/// The reported reader defects: the header panic, and bytes after the outer
/// element being accepted; delete once a fix reaches main.
pub fn has_known_reader_defect(blob: &[u8]) -> bool {
    has_known_panic(blob) || split_element(blob).is_some_and(|(_, consumed)| consumed != blob.len())
}
