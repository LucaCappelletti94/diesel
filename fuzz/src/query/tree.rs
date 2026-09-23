//! The expression trees the fuzzer draws, one enum per sql type.

use arbitrary::{Arbitrary, Unstructured};
use serde_json::Value;

/// Deepest operator nesting a generated tree reaches.
pub const MAX_DEPTH: usize = 8;

/// Longest `IN` list a generated tree holds.
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
}

#[derive(Debug)]
pub enum Text {
    Column(TextColumn),
    Literal(String),
    Concat(Box<Text>, Box<Text>),
    FromInt(Box<Int>),
    FromJson(Box<Json>),
    JsonField(Box<Json>, JsonKey),
}

#[derive(Debug)]
pub enum Json {
    Column,
    Literal(Value),
    Field(Box<Json>, JsonKey),
    FromText(Box<Text>),
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
        negated: bool,
        value: Box<Text>,
        pattern: Box<Text>,
        escape: Option<char>,
    },
    And(Box<Bool>, Box<Bool>),
    Or(Box<Bool>, Box<Bool>),
    Not(Box<Bool>),
}

/// `SELECT select FROM t [WHERE filter] ORDER BY t.id`, nested inside an expression.
#[derive(Debug)]
pub struct Subquery {
    pub select: Int,
    pub filter: Option<Bool>,
}

/// A second sort key after `t.id`, which keeps sqlite's row order fixed.
#[derive(Debug)]
pub struct Order {
    pub key: Int,
    pub descending: bool,
}

/// `SELECT [DISTINCT] int, text, bool FROM t [WHERE filter] ORDER BY t.id [, order]
/// [LIMIT limit] [OFFSET offset]`
#[derive(Debug)]
pub struct Query {
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

/// How much deeper a draw may still nest.
#[derive(Clone, Copy)]
struct Budget {
    depth: usize,
}

impl Budget {
    fn deeper(self) -> Self {
        Budget {
            depth: self.depth.saturating_sub(1),
        }
    }

    /// Picks among `leaves` alone once the depth runs out, else among all `variants`.
    fn choose(
        self,
        u: &mut Unstructured<'_>,
        leaves: usize,
        variants: usize,
    ) -> arbitrary::Result<usize> {
        u.choose_index(if self.depth == 0 { leaves } else { variants })
    }
}

impl<'a> Arbitrary<'a> for Input {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let budget = Budget { depth: MAX_DEPTH };
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
            distinct,
            int: Int::draw(u, budget)?,
            text: Text::draw(u, budget)?,
            bool: Bool::draw(u, budget)?,
            filter: option(u, |u| Bool::draw(u, budget))?,
            order: option(u, |u| {
                Ok(Order {
                    key: Int::draw(u, budget)?,
                    descending: u.arbitrary()?,
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
        Ok(match budget.choose(u, 2, 6)? {
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
            _ => Int::Scalar(boxed(Subquery::draw(u, deeper))?),
        })
    }
}

impl Text {
    fn draw(u: &mut Unstructured<'_>, budget: Budget) -> arbitrary::Result<Self> {
        let deeper = budget.deeper();
        Ok(match budget.choose(u, 2, 6)? {
            0 => Text::Column(u.arbitrary()?),
            1 => Text::Literal(u.arbitrary()?),
            2 => Text::Concat(boxed(Text::draw(u, deeper))?, boxed(Text::draw(u, deeper))?),
            3 => Text::FromInt(boxed(Int::draw(u, deeper))?),
            4 => Text::FromJson(boxed(Json::draw(u, deeper))?),
            _ => Text::JsonField(boxed(Json::draw(u, deeper))?, JsonKey::draw(u, deeper)?),
        })
    }
}

impl Json {
    fn draw(u: &mut Unstructured<'_>, budget: Budget) -> arbitrary::Result<Self> {
        let deeper = budget.deeper();
        Ok(match budget.choose(u, 2, 4)? {
            0 => Json::Column,
            1 => Json::Literal(json_value(u, 2)?),
            2 => Json::Field(boxed(Json::draw(u, deeper))?, JsonKey::draw(u, deeper)?),
            _ => Json::FromText(boxed(Text::draw(u, deeper))?),
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
        Ok(match budget.choose(u, 2, 15)? {
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
                negated: u.arbitrary()?,
                value: text(u)?,
                pattern: text(u)?,
                escape: u.arbitrary()?,
            },
            12 => Bool::And(boolean(u)?, boolean(u)?),
            13 => Bool::Or(boolean(u)?, boolean(u)?),
            _ => Bool::Not(boolean(u)?),
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
