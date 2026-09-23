//! The expression trees the fuzzer draws, one enum per sql type.
//!
//! Every `Postgres` variant and the types only it reaches exist for postgres alone. A query
//! draws them only when its `postgres` flag is set, and sqlite never sees such a query.

use arbitrary::{Arbitrary, Unstructured};
use chrono::{DateTime, NaiveDateTime, Utc};
use ipnetwork::IpNetwork;
use serde_json::Value;
use std::collections::Bound;

/// Deepest operator nesting a generated tree reaches.
pub const MAX_DEPTH: usize = 8;

/// Longest list a generated value holds, be it an `IN` list, an array or a json path.
const MAX_LIST: usize = 4;

#[derive(Arbitrary, Debug, Clone, Copy)]
pub enum IntColumn {
    A,
    B,
    G,
}

#[derive(Arbitrary, Debug, Clone, Copy)]
pub enum TextColumn {
    S,
    N,
}

#[derive(Arbitrary, Debug, Clone, Copy)]
pub enum Arith {
    Add,
    Sub,
    Mul,
    Div,
}

#[derive(Arbitrary, Debug, Clone, Copy)]
pub enum Comparison {
    Eq,
    NotEq,
    Lt,
    LtEq,
    Gt,
    GtEq,
}

/// Postgres renders each as its own operator, sqlite only knows `LIKE`.
#[derive(Arbitrary, Debug, Clone, Copy)]
pub enum Matcher {
    Like,
    ILike,
    SimilarTo,
}

#[derive(Debug)]
pub enum Int {
    Column(IntColumn),
    Literal(i32),
    Arith(Arith, Box<Int>, Box<Int>),
    Case {
        when: Box<Bool>,
        then: Box<Int>,
        second: Option<(Box<Bool>, Box<Int>)>,
        otherwise: Option<Box<Int>>,
    },
    FromText(Box<Text>),
    Scalar(Box<Subquery>),
    Postgres(PgInt),
}

#[derive(Debug)]
pub enum Text {
    Column(TextColumn),
    Literal(String),
    Concat(Box<Text>, Box<Text>),
    FromInt(Box<Int>),
    FromJson(Box<Json>),
    JsonField(Box<Json>, JsonKey),
    Postgres(PgText),
}

#[derive(Debug)]
pub enum Json {
    Column,
    Literal(Value),
    Field(Box<Json>, JsonKey),
    FromText(Box<Text>),
    Postgres(PgJson),
}

/// The right side of `->` and `->>`, a bound key or index, or an expression producing one.
#[derive(Debug)]
pub enum JsonKey {
    Name(String),
    Position(i32),
    Text(Box<Text>),
    Int(Box<Int>),
}

#[derive(Debug)]
pub enum Bool {
    Column,
    Literal(bool),
    Compare(Comparison, Box<Int>, Box<Int>),
    CompareText(Comparison, Box<Text>, Box<Text>),
    Between {
        negated: bool,
        value: Box<Int>,
        low: Box<Int>,
        high: Box<Int>,
    },
    In {
        negated: bool,
        value: Box<Int>,
        list: Vec<i32>,
    },
    InSubquery {
        negated: bool,
        value: Box<Int>,
        subquery: Box<Subquery>,
    },
    Exists(Box<Subquery>),
    IsNull {
        negated: bool,
        value: Box<Int>,
    },
    IsNullText {
        negated: bool,
        value: Box<Text>,
    },
    Distinct {
        negated: bool,
        left: Box<Int>,
        right: Box<Int>,
    },
    Match {
        matcher: Matcher,
        negated: bool,
        value: Box<Text>,
        pattern: Box<Text>,
        escape: Option<char>,
    },
    And(Box<Bool>, Box<Bool>),
    Or(Box<Bool>, Box<Bool>),
    Not(Box<Bool>),
    Postgres(PgBool),
}

/// `SELECT select FROM t [WHERE filter] ORDER BY t.id`, nested inside an expression.
#[derive(Debug)]
pub struct Subquery {
    pub select: Int,
    pub filter: Option<Bool>,
}

#[derive(Arbitrary, Debug, Clone, Copy)]
pub enum Nulls {
    First,
    Last,
}

/// A second sort key after `t.id`, which keeps sqlite's row order fixed.
#[derive(Debug)]
pub struct Order {
    pub key: Int,
    pub descending: bool,
    pub nulls: Option<Nulls>,
}

/// `SELECT [DISTINCT] int, text, bool FROM t [WHERE filter] ORDER BY t.id [, order]
/// [LIMIT limit] [OFFSET offset]`
#[derive(Debug)]
pub struct Query {
    pub postgres: bool,
    pub distinct: bool,
    pub int: Int,
    pub text: Text,
    pub bool: Bool,
    pub filter: Option<Bool>,
    pub order: Option<Order>,
    pub limit: Option<i64>,
    pub offset: Option<i64>,
}

/// An integer valid in a query grouped by `t.g`, the key itself or an aggregate.
#[derive(Debug)]
pub enum AggInt {
    Key,
    Literal(i32),
    Min(Box<Int>),
    Max(Box<Int>),
    Arith(Arith, Box<AggInt>, Box<AggInt>),
}

/// A `BigInt` aggregate.
#[derive(Debug)]
pub enum AggBig {
    Literal(i64),
    Sum(Box<Int>),
    Count(Box<Int>),
    CountStar,
}

/// A predicate valid in `HAVING`.
#[derive(Debug)]
pub enum AggBool {
    Literal(bool),
    Compare(Comparison, Box<AggInt>, Box<AggInt>),
    CompareBig(Comparison, Box<AggBig>, Box<AggBig>),
    IsNull { negated: bool, value: Box<AggInt> },
    And(Box<AggBool>, Box<AggBool>),
    Or(Box<AggBool>, Box<AggBool>),
    Not(Box<AggBool>),
}

/// `SELECT t.g, int, big FROM t [WHERE filter] GROUP BY t.g [HAVING having] ORDER BY t.g`
#[derive(Debug)]
pub struct Grouping {
    pub postgres: bool,
    pub int: AggInt,
    pub big: AggBig,
    pub filter: Option<Bool>,
    pub having: Option<AggBool>,
}

/// One fuzz input, a plain query or a grouped one.
#[derive(Debug)]
pub enum Input {
    Rows(Query),
    Groups(Grouping),
}

#[derive(Debug)]
pub enum PgInt {
    FromBool(Box<Bool>),
    Index(Box<IntArray>, Box<Int>),
    IndexLiteral(Box<IntArray>, i32),
}

#[derive(Debug)]
pub enum PgText {
    FromBool(Box<Bool>),
    FromJsonb(Box<Jsonb>),
    FromNet(Box<Net>),
    JsonbField(Box<Jsonb>, JsonKey),
    JsonbPath(Box<Jsonb>, Vec<String>),
}

#[derive(Debug)]
pub enum PgJson {
    FromJsonb(Box<Jsonb>),
}

#[derive(Arbitrary, Debug, Clone, Copy)]
pub enum JsonKind {
    Any,
    Object,
    Array,
    Scalar,
}

#[derive(Arbitrary, Debug, Clone, Copy)]
pub enum ArrayOp {
    Overlaps,
    Contains,
    IsContainedBy,
}

#[derive(Arbitrary, Debug, Clone, Copy)]
pub enum RangeOp {
    Contains,
    IsContainedBy,
    Overlaps,
    ExtendsRightTo,
    ExtendsLeftTo,
    LesserThan,
    GreaterThan,
    Adjacent,
}

#[derive(Arbitrary, Debug, Clone, Copy)]
pub enum NetOp {
    Contains,
    ContainsOrEq,
    IsContainedBy,
    IsContainedByOrEq,
    Overlaps,
}

#[derive(Debug)]
pub enum PgBool {
    FromInt(Box<Int>),
    HasKey(Box<Jsonb>, Box<Text>),
    HasAnyKey(Box<Jsonb>, Vec<String>),
    HasAllKeys(Box<Jsonb>, Vec<String>),
    JsonbContains(Box<Jsonb>, Box<Jsonb>),
    JsonbIsContainedBy(Box<Jsonb>, Box<Jsonb>),
    IsJson {
        kind: JsonKind,
        negated: bool,
        value: Box<Text>,
    },
    Array(ArrayOp, Box<IntArray>, Box<IntArray>),
    Range(RangeOp, Box<Range>, Box<Range>),
    RangeHas(Box<Range>, Box<Int>),
    InRange(Box<Int>, Box<Range>),
    Net(NetOp, Box<Net>, Box<Net>),
    NetDistance(Comparison, Box<Net>, Box<Net>, i64),
    Stamp(Comparison, Box<Stamp>, Box<Stamp>),
    StampTz(Comparison, Box<StampTz>, Box<StampTz>),
    BinaryMatch {
        negated: bool,
        value: Box<Binary>,
        pattern: Box<Binary>,
        escape: Option<char>,
    },
}

/// Which ends of `[low:high]` a slice spells out.
#[derive(Debug)]
pub enum Bounds<T> {
    Both(T, T),
    From(T),
    To(T),
}

#[derive(Debug)]
pub enum IntArray {
    Column,
    Literal(Vec<i32>),
    Concat(Box<IntArray>, Box<IntArray>),
    Build(Vec<Int>),
    FromSubquery(Box<Subquery>),
    Slice(Box<IntArray>, Bounds<Box<Int>>),
    SliceLiteral(Box<IntArray>, Bounds<i32>),
}

/// The right side of the jsonb `-` operator.
#[derive(Debug)]
pub enum RemoveKey {
    Name(String),
    Position(i32),
    Names(Vec<String>),
}

#[derive(Debug)]
pub enum Jsonb {
    Column,
    Literal(Value),
    Concat(Box<Jsonb>, Box<Jsonb>),
    Remove(Box<Jsonb>, RemoveKey),
    RemovePath(Box<Jsonb>, Vec<String>),
    Field(Box<Jsonb>, JsonKey),
    Path(Box<Jsonb>, Vec<String>),
    FromText(Box<Text>),
    FromJson(Box<Json>),
}

#[derive(Arbitrary, Debug, Clone, Copy)]
pub enum RangeCombine {
    Union,
    Difference,
    Intersection,
}

#[derive(Debug)]
pub enum Range {
    Column,
    Literal(Bound<i32>, Bound<i32>),
    Combine(RangeCombine, Box<Range>, Box<Range>),
}

#[derive(Arbitrary, Debug, Clone, Copy)]
pub enum NetMask {
    And,
    Or,
}

#[derive(Debug)]
pub enum Net {
    Column,
    Literal(IpNetwork),
    Mask(NetMask, Box<Net>, Box<Net>),
    FromText(Box<Text>),
}

#[derive(Debug)]
pub enum Stamp {
    Column,
    Literal(NaiveDateTime),
    /// Mirrors diesel's typing of `AT TIME ZONE`, a `Timestamp` for either input. Postgres
    /// returns a `timestamptz` for `Zoned::Stamp`, which diesel cannot tell apart from `now`
    /// (diesel-rs/diesel#1514).
    AtZone(Box<Zoned>, Box<Text>),
}

/// What `AT TIME ZONE` reads.
#[derive(Debug)]
pub enum Zoned {
    Stamp(Box<Stamp>),
    StampTz(Box<StampTz>),
}

#[derive(Debug)]
pub enum StampTz {
    Column,
    Literal(DateTime<Utc>),
}

#[derive(Debug)]
pub enum Binary {
    Column,
    Literal(Vec<u8>),
    Concat(Box<Binary>, Box<Binary>),
}

/// How much tree a draw may still build, and whether postgres-only nodes may appear in it.
#[derive(Clone, Copy)]
struct Budget {
    depth: usize,
    postgres: bool,
}

impl Budget {
    /// Guards every postgres-only node, which a sqlite query must never contain.
    fn assert_postgres(self) {
        assert!(
            self.postgres,
            "drew a postgres-only node for a sqlite query"
        );
    }

    fn deeper(self) -> Self {
        Budget {
            depth: self.depth.saturating_sub(1),
            postgres: self.postgres,
        }
    }

    /// Picks among `leaves` alone once the depth runs out, then among `shared` variants, then
    /// among all `variants` when postgres-only ones may appear.
    fn choose(
        self,
        u: &mut Unstructured<'_>,
        leaves: usize,
        shared: usize,
        variants: usize,
    ) -> arbitrary::Result<usize> {
        let count = match (self.depth, self.postgres) {
            (0, _) => leaves,
            (_, false) => shared,
            (_, true) => variants,
        };
        u.choose_index(count)
    }
}

impl<'a> Arbitrary<'a> for Input {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let budget = Budget {
            depth: MAX_DEPTH,
            postgres: u.arbitrary()?,
        };
        Ok(if u.arbitrary()? {
            Input::Groups(Grouping::draw(u, budget)?)
        } else {
            Input::Rows(Query::draw(u, budget)?)
        })
    }
}

/// Largest `LIMIT` or `OFFSET` drawn, a little past the fixture's five rows.
const MAX_PAGE: i64 = 6;

impl Query {
    fn draw(u: &mut Unstructured<'_>, budget: Budget) -> arbitrary::Result<Self> {
        let distinct = u.arbitrary()?;
        // sqlite keeps an arbitrary row of each duplicate, so a page of a distinct query could
        // differ between two spellings of the same query
        let page = |u: &mut Unstructured<'_>| -> arbitrary::Result<Option<i64>> {
            if distinct {
                Ok(None)
            } else {
                option(u, |u| u.int_in_range(0..=MAX_PAGE))
            }
        };
        Ok(Query {
            postgres: budget.postgres,
            distinct,
            int: Int::draw(u, budget)?,
            text: Text::draw(u, budget)?,
            bool: Bool::draw(u, budget)?,
            filter: option(u, |u| Bool::draw(u, budget))?,
            order: option(u, |u| {
                Ok(Order {
                    key: Int::draw(u, budget)?,
                    descending: u.arbitrary()?,
                    nulls: if budget.postgres {
                        u.arbitrary()?
                    } else {
                        None
                    },
                })
            })?,
            limit: page(u)?,
            offset: page(u)?,
        })
    }
}

impl Grouping {
    fn draw(u: &mut Unstructured<'_>, budget: Budget) -> arbitrary::Result<Self> {
        Ok(Grouping {
            postgres: budget.postgres,
            int: AggInt::draw(u, budget)?,
            big: AggBig::draw(u, budget)?,
            filter: option(u, |u| Bool::draw(u, budget))?,
            having: option(u, |u| AggBool::draw(u, budget))?,
        })
    }
}

impl AggInt {
    fn draw(u: &mut Unstructured<'_>, budget: Budget) -> arbitrary::Result<Self> {
        let deeper = budget.deeper();
        let variants = if budget.depth == 0 { 2 } else { 5 };
        Ok(match u.choose_index(variants)? {
            0 => AggInt::Key,
            1 => AggInt::Literal(u.arbitrary()?),
            2 => AggInt::Min(boxed(Int::draw(u, deeper))?),
            3 => AggInt::Max(boxed(Int::draw(u, deeper))?),
            _ => AggInt::Arith(
                u.arbitrary()?,
                boxed(AggInt::draw(u, deeper))?,
                boxed(AggInt::draw(u, deeper))?,
            ),
        })
    }
}

impl AggBig {
    fn draw(u: &mut Unstructured<'_>, budget: Budget) -> arbitrary::Result<Self> {
        let deeper = budget.deeper();
        let variants = if budget.depth == 0 { 2 } else { 4 };
        Ok(match u.choose_index(variants)? {
            0 => AggBig::Literal(u.arbitrary()?),
            1 => AggBig::CountStar,
            2 => AggBig::Sum(boxed(Int::draw(u, deeper))?),
            _ => AggBig::Count(boxed(Int::draw(u, deeper))?),
        })
    }
}

impl AggBool {
    fn draw(u: &mut Unstructured<'_>, budget: Budget) -> arbitrary::Result<Self> {
        let deeper = budget.deeper();
        let int = |u: &mut Unstructured<'_>| boxed(AggInt::draw(u, deeper));
        let big = |u: &mut Unstructured<'_>| boxed(AggBig::draw(u, deeper));
        let boolean = |u: &mut Unstructured<'_>| boxed(AggBool::draw(u, deeper));
        let variants = if budget.depth == 0 { 1 } else { 7 };
        Ok(match u.choose_index(variants)? {
            0 => AggBool::Literal(u.arbitrary()?),
            1 => AggBool::Compare(u.arbitrary()?, int(u)?, int(u)?),
            2 => AggBool::CompareBig(u.arbitrary()?, big(u)?, big(u)?),
            3 => AggBool::IsNull {
                negated: u.arbitrary()?,
                value: int(u)?,
            },
            4 => AggBool::And(boolean(u)?, boolean(u)?),
            5 => AggBool::Or(boolean(u)?, boolean(u)?),
            _ => AggBool::Not(boolean(u)?),
        })
    }
}

fn option<T>(
    u: &mut Unstructured<'_>,
    draw: impl FnOnce(&mut Unstructured<'_>) -> arbitrary::Result<T>,
) -> arbitrary::Result<Option<T>> {
    Ok(if u.arbitrary()? { Some(draw(u)?) } else { None })
}

fn list<T>(
    u: &mut Unstructured<'_>,
    mut draw: impl FnMut(&mut Unstructured<'_>) -> arbitrary::Result<T>,
) -> arbitrary::Result<Vec<T>> {
    let mut items = Vec::new();
    for _ in 0..u.int_in_range(0..=MAX_LIST)? {
        items.push(draw(u)?);
    }
    Ok(items)
}

fn boxed<T>(value: arbitrary::Result<T>) -> arbitrary::Result<Box<T>> {
    value.map(Box::new)
}

impl Int {
    fn draw(u: &mut Unstructured<'_>, budget: Budget) -> arbitrary::Result<Self> {
        let deeper = budget.deeper();
        Ok(match budget.choose(u, 2, 6, 7)? {
            0 => Int::Column(u.arbitrary()?),
            1 => Int::Literal(u.arbitrary()?),
            2 => Int::Arith(
                u.arbitrary()?,
                boxed(Int::draw(u, deeper))?,
                boxed(Int::draw(u, deeper))?,
            ),
            3 => Int::Case {
                when: boxed(Bool::draw(u, deeper))?,
                then: boxed(Int::draw(u, deeper))?,
                second: option(u, |u| {
                    Ok((boxed(Bool::draw(u, deeper))?, boxed(Int::draw(u, deeper))?))
                })?,
                otherwise: option(u, |u| boxed(Int::draw(u, deeper)))?,
            },
            4 => Int::FromText(boxed(Text::draw(u, deeper))?),
            5 => Int::Scalar(boxed(Subquery::draw(u, deeper))?),
            _ => {
                budget.assert_postgres();
                Int::Postgres(match u.choose_index(3)? {
                    0 => PgInt::FromBool(boxed(Bool::draw(u, deeper))?),
                    1 => PgInt::Index(
                        boxed(IntArray::draw(u, deeper))?,
                        boxed(Int::draw(u, deeper))?,
                    ),
                    _ => PgInt::IndexLiteral(boxed(IntArray::draw(u, deeper))?, u.arbitrary()?),
                })
            }
        })
    }
}

impl Text {
    fn draw(u: &mut Unstructured<'_>, budget: Budget) -> arbitrary::Result<Self> {
        let deeper = budget.deeper();
        Ok(match budget.choose(u, 2, 6, 7)? {
            0 => Text::Column(u.arbitrary()?),
            1 => Text::Literal(u.arbitrary()?),
            2 => Text::Concat(boxed(Text::draw(u, deeper))?, boxed(Text::draw(u, deeper))?),
            3 => Text::FromInt(boxed(Int::draw(u, deeper))?),
            4 => Text::FromJson(boxed(Json::draw(u, deeper))?),
            5 => Text::JsonField(boxed(Json::draw(u, deeper))?, JsonKey::draw(u, deeper)?),
            _ => {
                budget.assert_postgres();
                Text::Postgres(match u.choose_index(5)? {
                    0 => PgText::FromBool(boxed(Bool::draw(u, deeper))?),
                    1 => PgText::FromJsonb(boxed(Jsonb::draw(u, deeper))?),
                    2 => PgText::FromNet(boxed(Net::draw(u, deeper))?),
                    3 => PgText::JsonbField(
                        boxed(Jsonb::draw(u, deeper))?,
                        JsonKey::draw(u, deeper)?,
                    ),
                    _ => PgText::JsonbPath(
                        boxed(Jsonb::draw(u, deeper))?,
                        list(u, |u| u.arbitrary())?,
                    ),
                })
            }
        })
    }
}

impl Json {
    fn draw(u: &mut Unstructured<'_>, budget: Budget) -> arbitrary::Result<Self> {
        let deeper = budget.deeper();
        Ok(match budget.choose(u, 2, 4, 5)? {
            0 => Json::Column,
            1 => Json::Literal(json_value(u, 2)?),
            2 => Json::Field(boxed(Json::draw(u, deeper))?, JsonKey::draw(u, deeper)?),
            3 => Json::FromText(boxed(Text::draw(u, deeper))?),
            _ => {
                budget.assert_postgres();
                Json::Postgres(PgJson::FromJsonb(boxed(Jsonb::draw(u, deeper))?))
            }
        })
    }
}

impl JsonKey {
    fn draw(u: &mut Unstructured<'_>, budget: Budget) -> arbitrary::Result<Self> {
        let deeper = budget.deeper();
        let variants = if budget.depth == 0 { 2 } else { 4 };
        Ok(match u.choose_index(variants)? {
            0 => JsonKey::Name(u.arbitrary()?),
            1 => JsonKey::Position(u.arbitrary()?),
            2 => JsonKey::Text(boxed(Text::draw(u, deeper))?),
            _ => JsonKey::Int(boxed(Int::draw(u, deeper))?),
        })
    }
}

impl Subquery {
    fn draw(u: &mut Unstructured<'_>, budget: Budget) -> arbitrary::Result<Self> {
        Ok(Subquery {
            select: Int::draw(u, budget)?,
            filter: option(u, |u| Bool::draw(u, budget))?,
        })
    }
}

impl Bool {
    fn draw(u: &mut Unstructured<'_>, budget: Budget) -> arbitrary::Result<Self> {
        let deeper = budget.deeper();
        let int = |u: &mut Unstructured<'_>| boxed(Int::draw(u, deeper));
        let text = |u: &mut Unstructured<'_>| boxed(Text::draw(u, deeper));
        let boolean = |u: &mut Unstructured<'_>| boxed(Bool::draw(u, deeper));
        Ok(match budget.choose(u, 2, 15, 16)? {
            0 => Bool::Column,
            1 => Bool::Literal(u.arbitrary()?),
            2 => Bool::Compare(u.arbitrary()?, int(u)?, int(u)?),
            3 => Bool::CompareText(u.arbitrary()?, text(u)?, text(u)?),
            4 => Bool::Between {
                negated: u.arbitrary()?,
                value: int(u)?,
                low: int(u)?,
                high: int(u)?,
            },
            5 => Bool::In {
                negated: u.arbitrary()?,
                value: int(u)?,
                list: list(u, |u| u.arbitrary())?,
            },
            6 => Bool::InSubquery {
                negated: u.arbitrary()?,
                value: int(u)?,
                subquery: boxed(Subquery::draw(u, deeper))?,
            },
            7 => Bool::Exists(boxed(Subquery::draw(u, deeper))?),
            8 => Bool::IsNull {
                negated: u.arbitrary()?,
                value: int(u)?,
            },
            9 => Bool::IsNullText {
                negated: u.arbitrary()?,
                value: text(u)?,
            },
            10 => Bool::Distinct {
                negated: u.arbitrary()?,
                left: int(u)?,
                right: int(u)?,
            },
            11 => Bool::Match {
                matcher: u.arbitrary()?,
                negated: u.arbitrary()?,
                value: text(u)?,
                pattern: text(u)?,
                escape: u.arbitrary()?,
            },
            12 => Bool::And(boolean(u)?, boolean(u)?),
            13 => Bool::Or(boolean(u)?, boolean(u)?),
            14 => Bool::Not(boolean(u)?),
            _ => {
                budget.assert_postgres();
                Bool::Postgres(PgBool::draw(u, deeper)?)
            }
        })
    }
}

impl PgBool {
    fn draw(u: &mut Unstructured<'_>, budget: Budget) -> arbitrary::Result<Self> {
        let int = |u: &mut Unstructured<'_>| boxed(Int::draw(u, budget));
        let text = |u: &mut Unstructured<'_>| boxed(Text::draw(u, budget));
        let jsonb = |u: &mut Unstructured<'_>| boxed(Jsonb::draw(u, budget));
        let array = |u: &mut Unstructured<'_>| boxed(IntArray::draw(u, budget));
        let range = |u: &mut Unstructured<'_>| boxed(Range::draw(u, budget));
        let net = |u: &mut Unstructured<'_>| boxed(Net::draw(u, budget));
        let binary = |u: &mut Unstructured<'_>| boxed(Binary::draw(u, budget));
        Ok(match u.choose_index(16)? {
            0 => PgBool::FromInt(int(u)?),
            1 => PgBool::HasKey(jsonb(u)?, text(u)?),
            2 => PgBool::HasAnyKey(jsonb(u)?, list(u, |u| u.arbitrary())?),
            3 => PgBool::HasAllKeys(jsonb(u)?, list(u, |u| u.arbitrary())?),
            4 => PgBool::JsonbContains(jsonb(u)?, jsonb(u)?),
            5 => PgBool::JsonbIsContainedBy(jsonb(u)?, jsonb(u)?),
            6 => PgBool::IsJson {
                kind: u.arbitrary()?,
                negated: u.arbitrary()?,
                value: text(u)?,
            },
            7 => PgBool::Array(u.arbitrary()?, array(u)?, array(u)?),
            8 => PgBool::Range(u.arbitrary()?, range(u)?, range(u)?),
            9 => PgBool::RangeHas(range(u)?, int(u)?),
            10 => PgBool::InRange(int(u)?, range(u)?),
            11 => PgBool::Net(u.arbitrary()?, net(u)?, net(u)?),
            12 => PgBool::NetDistance(u.arbitrary()?, net(u)?, net(u)?, u.arbitrary()?),
            13 => PgBool::Stamp(
                u.arbitrary()?,
                boxed(Stamp::draw(u, budget))?,
                boxed(Stamp::draw(u, budget))?,
            ),
            14 => PgBool::StampTz(
                u.arbitrary()?,
                boxed(StampTz::draw(u))?,
                boxed(StampTz::draw(u))?,
            ),
            _ => PgBool::BinaryMatch {
                negated: u.arbitrary()?,
                value: binary(u)?,
                pattern: binary(u)?,
                escape: u.arbitrary()?,
            },
        })
    }
}

impl<T> Bounds<T> {
    fn draw(
        u: &mut Unstructured<'_>,
        mut end: impl FnMut(&mut Unstructured<'_>) -> arbitrary::Result<T>,
    ) -> arbitrary::Result<Self> {
        Ok(match u.choose_index(3)? {
            0 => Bounds::Both(end(u)?, end(u)?),
            1 => Bounds::From(end(u)?),
            _ => Bounds::To(end(u)?),
        })
    }
}

impl IntArray {
    fn draw(u: &mut Unstructured<'_>, budget: Budget) -> arbitrary::Result<Self> {
        let deeper = budget.deeper();
        let array = |u: &mut Unstructured<'_>| boxed(IntArray::draw(u, deeper));
        Ok(match budget.choose(u, 2, 7, 7)? {
            0 => IntArray::Column,
            1 => IntArray::Literal(list(u, |u| u.arbitrary())?),
            2 => IntArray::Concat(array(u)?, array(u)?),
            3 => IntArray::Build({
                let mut items = vec![Int::draw(u, deeper)?];
                for _ in 0..u.int_in_range(0..=2)? {
                    items.push(Int::draw(u, deeper)?);
                }
                items
            }),
            4 => IntArray::FromSubquery(boxed(Subquery::draw(u, deeper))?),
            5 => IntArray::Slice(array(u)?, Bounds::draw(u, |u| boxed(Int::draw(u, deeper)))?),
            _ => IntArray::SliceLiteral(array(u)?, Bounds::draw(u, |u| u.arbitrary())?),
        })
    }
}

impl Jsonb {
    fn draw(u: &mut Unstructured<'_>, budget: Budget) -> arbitrary::Result<Self> {
        let deeper = budget.deeper();
        let jsonb = |u: &mut Unstructured<'_>| boxed(Jsonb::draw(u, deeper));
        Ok(match budget.choose(u, 2, 9, 9)? {
            0 => Jsonb::Column,
            1 => Jsonb::Literal(json_value(u, 2)?),
            2 => Jsonb::Concat(jsonb(u)?, jsonb(u)?),
            3 => Jsonb::Remove(
                jsonb(u)?,
                match u.choose_index(3)? {
                    0 => RemoveKey::Name(u.arbitrary()?),
                    1 => RemoveKey::Position(u.arbitrary()?),
                    _ => RemoveKey::Names(list(u, |u| u.arbitrary())?),
                },
            ),
            4 => Jsonb::RemovePath(jsonb(u)?, list(u, |u| u.arbitrary())?),
            5 => Jsonb::Field(jsonb(u)?, JsonKey::draw(u, deeper)?),
            6 => Jsonb::Path(jsonb(u)?, list(u, |u| u.arbitrary())?),
            7 => Jsonb::FromText(boxed(Text::draw(u, deeper))?),
            _ => Jsonb::FromJson(boxed(Json::draw(u, deeper))?),
        })
    }
}

impl Range {
    fn draw(u: &mut Unstructured<'_>, budget: Budget) -> arbitrary::Result<Self> {
        let deeper = budget.deeper();
        Ok(match budget.choose(u, 2, 3, 3)? {
            0 => Range::Column,
            1 => Range::Literal(bound(u)?, bound(u)?),
            _ => Range::Combine(
                u.arbitrary()?,
                boxed(Range::draw(u, deeper))?,
                boxed(Range::draw(u, deeper))?,
            ),
        })
    }
}

fn bound(u: &mut Unstructured<'_>) -> arbitrary::Result<Bound<i32>> {
    Ok(match u.choose_index(3)? {
        0 => Bound::Included(u.arbitrary()?),
        1 => Bound::Excluded(u.arbitrary()?),
        _ => Bound::Unbounded,
    })
}

impl Net {
    fn draw(u: &mut Unstructured<'_>, budget: Budget) -> arbitrary::Result<Self> {
        let deeper = budget.deeper();
        Ok(match budget.choose(u, 2, 4, 4)? {
            0 => Net::Column,
            1 => Net::Literal(network(u)?),
            2 => Net::Mask(
                u.arbitrary()?,
                boxed(Net::draw(u, deeper))?,
                boxed(Net::draw(u, deeper))?,
            ),
            _ => Net::FromText(boxed(Text::draw(u, deeper))?),
        })
    }
}

fn network(u: &mut Unstructured<'_>) -> arbitrary::Result<IpNetwork> {
    let (address, width): (std::net::IpAddr, u8) = if u.arbitrary()? {
        (std::net::Ipv4Addr::from(u.arbitrary::<u32>()?).into(), 32)
    } else {
        (std::net::Ipv6Addr::from(u.arbitrary::<u128>()?).into(), 128)
    };
    let prefix = u.int_in_range(0..=width)?;
    Ok(IpNetwork::new(address, prefix).expect("a prefix within the address width"))
}

impl Stamp {
    fn draw(u: &mut Unstructured<'_>, budget: Budget) -> arbitrary::Result<Self> {
        let deeper = budget.deeper();
        Ok(match budget.choose(u, 2, 3, 3)? {
            0 => Stamp::Column,
            1 => Stamp::Literal(instant(u)?.naive_utc()),
            _ => Stamp::AtZone(
                Box::new(if u.arbitrary()? {
                    Zoned::Stamp(boxed(Stamp::draw(u, deeper))?)
                } else {
                    Zoned::StampTz(boxed(StampTz::draw(u))?)
                }),
                boxed(Text::draw(u, deeper))?,
            ),
        })
    }
}

impl StampTz {
    fn draw(u: &mut Unstructured<'_>) -> arbitrary::Result<Self> {
        Ok(if u.arbitrary()? {
            StampTz::Column
        } else {
            StampTz::Literal(instant(u)?)
        })
    }
}

fn instant(u: &mut Unstructured<'_>) -> arbitrary::Result<DateTime<Utc>> {
    let seconds = i64::from(u.arbitrary::<i32>()?);
    Ok(DateTime::from_timestamp(seconds, 0).expect("an i32 of seconds is a valid instant"))
}

impl Binary {
    fn draw(u: &mut Unstructured<'_>, budget: Budget) -> arbitrary::Result<Self> {
        let deeper = budget.deeper();
        Ok(match budget.choose(u, 2, 3, 3)? {
            0 => Binary::Column,
            1 => Binary::Literal(u.arbitrary()?),
            _ => Binary::Concat(
                boxed(Binary::draw(u, deeper))?,
                boxed(Binary::draw(u, deeper))?,
            ),
        })
    }
}

/// A json document at most `depth` containers deep, small enough to keep inputs short.
fn json_value(u: &mut Unstructured<'_>, depth: usize) -> arbitrary::Result<Value> {
    let variants = if depth == 0 { 4 } else { 6 };
    Ok(match u.choose_index(variants)? {
        0 => Value::Null,
        1 => Value::Bool(u.arbitrary()?),
        2 => Value::from(u.arbitrary::<i32>()?),
        3 => Value::String(u.arbitrary()?),
        4 => Value::Array(list(u, |u| json_value(u, depth - 1))?),
        _ => Value::Object(
            list(u, |u| {
                Ok((u.arbitrary::<String>()?, json_value(u, depth - 1)?))
            })?
            .into_iter()
            .collect(),
        ),
    })
}
