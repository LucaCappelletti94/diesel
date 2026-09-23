//! Postgres' own parser reads the sql diesel renders, and its parse tree must nest the operators
//! the way the expression tree does.

use super::{
    ArrayOp, Binary, Bounds, IntArray, JsonKind, Jsonb, Matcher, Net, NetMask, NetOp, Nulls,
    PgBool, PgInt, PgJson, PgText, Range, RangeCombine, RangeOp, RemoveKey, Stamp, StampTz, Zoned,
};
use diesel::pg::{Pg, PgQueryBuilder};
use diesel::query_builder::QueryBuilder;
use diesel::sql_types::{
    Array, Binary as SqlBinary, Inet, Int4range, Jsonb as SqlJsonb, Timestamp, Timestamptz,
};
use pg_query::NodeEnum;
use pg_query::protobuf::{
    AExprKind, BoolExprType, JsonValueType, Node, NullTestType, SelectStmt, SortByDir, SortByNulls,
    SubLinkType,
};
use std::fmt;

builder!(Pg);

type Ints = Array<Integer>;

fn distinct<'a>(
    negated: bool,
    left: Boxed<'a, Integer>,
    right: Boxed<'a, Integer>,
) -> Boxed<'a, SqlBool> {
    if negated {
        Box::new(left.is_not_distinct_from(right).nullable())
    } else {
        Box::new(left.is_distinct_from(right).nullable())
    }
}

macro_rules! escaped {
    ($matched:expr, $escape:expr) => {{
        let matched = $matched;
        let escaped: Boxed<'_, SqlBool> = match $escape {
            Some(character) => Box::new(matched.escape(character)),
            None => Box::new(matched),
        };
        escaped
    }};
}

fn matches<'a>(
    matcher: Matcher,
    negated: bool,
    value: Boxed<'a, SqlText>,
    pattern: Boxed<'a, SqlText>,
    escape: Option<char>,
) -> Boxed<'a, SqlBool> {
    // postgres' own matchers take a pattern that is not null
    match (matcher, negated) {
        (Matcher::Like, false) => escaped!(value.like(pattern), escape),
        (Matcher::Like, true) => escaped!(value.not_like(pattern), escape),
        (Matcher::ILike, false) => escaped!(value.ilike(pattern.assume_not_null()), escape),
        (Matcher::ILike, true) => escaped!(value.not_ilike(pattern.assume_not_null()), escape),
        (Matcher::SimilarTo, false) => {
            escaped!(value.similar_to(pattern.assume_not_null()), escape)
        }
        (Matcher::SimilarTo, true) => {
            escaped!(value.not_similar_to(pattern.assume_not_null()), escape)
        }
    }
}

fn json_field<'a>(value: Boxed<'a, SqlJson>, key: &'a JsonKey) -> Boxed<'a, SqlJson> {
    keyed!(key, |key| Box::new(value.retrieve_as_object(key)))
}

fn nulls_order<'a>(
    statement: Statement<'a>,
    key: Boxed<'a, Integer>,
    descending: bool,
    nulls: Nulls,
) -> Statement<'a> {
    match (descending, nulls) {
        (false, Nulls::First) => statement.then_order_by(key.asc().nulls_first()),
        (false, Nulls::Last) => statement.then_order_by(key.asc().nulls_last()),
        (true, Nulls::First) => statement.then_order_by(key.desc().nulls_first()),
        (true, Nulls::Last) => statement.then_order_by(key.desc().nulls_last()),
    }
}

fn postgres_int(tree: &PgInt) -> Boxed<'_, Integer> {
    match tree {
        PgInt::FromBool(value) => Box::new(boolean(value).cast::<Nullable<Integer>>()),
        PgInt::Index(array, index) => Box::new(ints(array).index_nullable(int(index))),
        PgInt::IndexLiteral(array, index) => Box::new(ints(array).index(*index)),
    }
}

fn postgres_text(tree: &PgText) -> Boxed<'_, SqlText> {
    match tree {
        PgText::FromBool(value) => Box::new(boolean(value).cast::<Nullable<SqlText>>()),
        PgText::FromJsonb(value) => Box::new(jsonb(value).cast::<Nullable<SqlText>>()),
        PgText::FromNet(value) => Box::new(net(value).cast::<Nullable<SqlText>>()),
        PgText::JsonbField(value, key) => {
            keyed!(key, |key| Box::new(jsonb(value).retrieve_as_text(key)))
        }
        PgText::JsonbPath(value, path) => Box::new(jsonb(value).retrieve_by_path_as_text(path)),
    }
}

fn postgres_json(tree: &PgJson) -> Boxed<'_, SqlJson> {
    match tree {
        PgJson::FromJsonb(value) => Box::new(jsonb(value).cast::<Nullable<SqlJson>>()),
    }
}

fn ints(tree: &IntArray) -> Boxed<'_, Ints> {
    use diesel::dsl::array;
    match tree {
        IntArray::Column => Box::new(t::ia),
        IntArray::Literal(values) => Box::new(values.into_sql::<Nullable<Ints>>()),
        IntArray::Concat(left, right) => {
            Box::new(PgArrayExpressionMethods::concat(ints(left), ints(right)))
        }
        IntArray::Build(items) => {
            let item = |tree| int(tree).assume_not_null();
            match items.as_slice() {
                [a] => Box::new(array::<Integer, _>((item(a),)).nullable()),
                [a, b] => Box::new(array::<Integer, _>((item(a), item(b))).nullable()),
                [a, b, c] => Box::new(array::<Integer, _>((item(a), item(b), item(c))).nullable()),
                _ => unreachable!("the generator builds arrays of one to three items"),
            }
        }
        IntArray::FromSubquery(subquery) => {
            let subselect = t::table
                .select(int(&subquery.select).assume_not_null())
                .order(t::id)
                .into_boxed();
            let subselect = match &subquery.filter {
                Some(filter) => subselect.filter(boolean(filter)),
                None => subselect,
            };
            Box::new(array::<Integer, _>(subselect).nullable())
        }
        IntArray::Slice(array, Bounds::Both(low, high)) => {
            Box::new(ints(array).slice_nullable(int(low), int(high)))
        }
        IntArray::Slice(array, Bounds::From(low)) => {
            Box::new(ints(array).slice_from_nullable(int(low)))
        }
        IntArray::Slice(array, Bounds::To(high)) => {
            Box::new(ints(array).slice_to_nullable(int(high)))
        }
        IntArray::SliceLiteral(array, Bounds::Both(low, high)) => {
            Box::new(ints(array).slice(*low, *high))
        }
        IntArray::SliceLiteral(array, Bounds::From(low)) => Box::new(ints(array).slice_from(*low)),
        IntArray::SliceLiteral(array, Bounds::To(high)) => Box::new(ints(array).slice_to(*high)),
    }
}

fn jsonb(tree: &Jsonb) -> Boxed<'_, SqlJsonb> {
    match tree {
        Jsonb::Column => Box::new(t::jb),
        Jsonb::Literal(value) => Box::new(value.into_sql::<Nullable<SqlJsonb>>()),
        Jsonb::Concat(left, right) => {
            Box::new(PgJsonbExpressionMethods::concat(jsonb(left), jsonb(right)))
        }
        Jsonb::Remove(value, RemoveKey::Name(name)) => Box::new(jsonb(value).remove(name.as_str())),
        Jsonb::Remove(value, RemoveKey::Position(position)) => {
            Box::new(jsonb(value).remove(*position))
        }
        Jsonb::Remove(value, RemoveKey::Names(names)) => {
            Box::new(jsonb(value).remove(names.iter().map(String::as_str).collect::<Vec<_>>()))
        }
        Jsonb::RemovePath(value, path) => Box::new(jsonb(value).remove_by_path(path)),
        Jsonb::Field(value, key) => {
            keyed!(key, |key| Box::new(jsonb(value).retrieve_as_object(key)))
        }
        Jsonb::Path(value, path) => Box::new(jsonb(value).retrieve_by_path_as_object(path)),
        Jsonb::FromText(value) => Box::new(text(value).fallible_cast::<Nullable<SqlJsonb>>()),
        Jsonb::FromJson(value) => Box::new(json(value).cast::<Nullable<SqlJsonb>>()),
    }
}

fn range(tree: &Range) -> Boxed<'_, Int4range> {
    match tree {
        Range::Column => Box::new(t::r),
        Range::Literal(low, high) => Box::new((*low, *high).into_sql::<Nullable<Int4range>>()),
        Range::Combine(RangeCombine::Union, left, right) => {
            Box::new(range(left).union_range(range(right)))
        }
        Range::Combine(RangeCombine::Difference, left, right) => {
            Box::new(range(left).difference_range(range(right)))
        }
        Range::Combine(RangeCombine::Intersection, left, right) => {
            Box::new(range(left).intersection_range(range(right)))
        }
    }
}

fn net(tree: &Net) -> Boxed<'_, Inet> {
    match tree {
        Net::Column => Box::new(t::ip),
        Net::Literal(network) => Box::new(network.into_sql::<Nullable<Inet>>()),
        Net::Mask(NetMask::And, left, right) => Box::new(PgNetExpressionMethods::and(
            net(left),
            net(right).assume_not_null(),
        )),
        Net::Mask(NetMask::Or, left, right) => Box::new(PgNetExpressionMethods::or(
            net(left),
            net(right).assume_not_null(),
        )),
        Net::FromText(value) => Box::new(text(value).fallible_cast::<Nullable<Inet>>()),
    }
}

/// Diesel types every `AT TIME ZONE` as a `Timestamp` that is never null, whatever it reads.
fn stamp(tree: &Stamp) -> Boxed<'_, Timestamp> {
    match tree {
        Stamp::Column => Box::new(t::ts),
        Stamp::Literal(instant) => Box::new(instant.into_sql::<Nullable<Timestamp>>()),
        Stamp::AtZone(instant, zone) => {
            let zone = text(zone).assume_not_null();
            match instant.as_ref() {
                Zoned::Stamp(instant) => Box::new(stamp(instant).at_time_zone(zone).nullable()),
                Zoned::StampTz(instant) => {
                    Box::new(stamp_tz(instant).at_time_zone(zone).nullable())
                }
            }
        }
    }
}

fn stamp_tz(tree: &StampTz) -> Boxed<'_, Timestamptz> {
    match tree {
        StampTz::Column => Box::new(t::tz),
        StampTz::Literal(instant) => Box::new(instant.into_sql::<Nullable<Timestamptz>>()),
    }
}

fn binary(tree: &Binary) -> Boxed<'_, SqlBinary> {
    match tree {
        Binary::Column => Box::new(t::bin),
        Binary::Literal(bytes) => Box::new(bytes.as_slice().into_sql::<Nullable<SqlBinary>>()),
        Binary::Concat(left, right) => Box::new(PgBinaryExpressionMethods::concat(
            binary(left),
            binary(right),
        )),
    }
}

fn postgres_bool(tree: &PgBool) -> Boxed<'_, SqlBool> {
    match tree {
        PgBool::FromInt(value) => Box::new(int(value).cast::<Nullable<SqlBool>>()),
        PgBool::HasKey(value, key) => Box::new(jsonb(value).has_key(text(key).assume_not_null())),
        PgBool::HasAnyKey(value, keys) => Box::new(jsonb(value).has_any_key(keys)),
        PgBool::HasAllKeys(value, keys) => Box::new(jsonb(value).has_all_keys(keys)),
        PgBool::JsonbContains(left, right) => Box::new(PgJsonbExpressionMethods::contains(
            jsonb(left),
            jsonb(right),
        )),
        PgBool::JsonbIsContainedBy(left, right) => Box::new(
            PgJsonbExpressionMethods::is_contained_by(jsonb(left), jsonb(right)),
        ),
        PgBool::IsJson {
            kind,
            negated,
            value,
        } => {
            let value = text(value);
            match (kind, negated) {
                (JsonKind::Any, false) => Box::new(value.is_json()),
                (JsonKind::Any, true) => Box::new(value.is_not_json()),
                (JsonKind::Object, false) => Box::new(value.is_json_object()),
                (JsonKind::Object, true) => Box::new(value.is_not_json_object()),
                (JsonKind::Array, false) => Box::new(value.is_json_array()),
                (JsonKind::Array, true) => Box::new(value.is_not_json_array()),
                (JsonKind::Scalar, false) => Box::new(value.is_json_scalar()),
                (JsonKind::Scalar, true) => Box::new(value.is_not_json_scalar()),
            }
        }
        PgBool::Array(op, left, right) => {
            let (left, right) = (ints(left), ints(right));
            match op {
                ArrayOp::Overlaps => Box::new(PgArrayExpressionMethods::overlaps_with(left, right)),
                ArrayOp::Contains => Box::new(PgArrayExpressionMethods::contains(left, right)),
                ArrayOp::IsContainedBy => {
                    Box::new(PgArrayExpressionMethods::is_contained_by(left, right))
                }
            }
        }
        PgBool::Range(op, left, right) => {
            let (left, right) = (range(left), range(right));
            match op {
                RangeOp::Contains => Box::new(left.contains_range(right)),
                RangeOp::IsContainedBy => {
                    Box::new(PgRangeExpressionMethods::is_contained_by(left, right))
                }
                RangeOp::Overlaps => Box::new(PgRangeExpressionMethods::overlaps_with(left, right)),
                RangeOp::ExtendsRightTo => Box::new(left.range_extends_right_to(right)),
                RangeOp::ExtendsLeftTo => Box::new(left.range_extends_left_to(right)),
                RangeOp::LesserThan => Box::new(left.lesser_than(right)),
                RangeOp::GreaterThan => Box::new(left.greater_than(right)),
                RangeOp::Adjacent => Box::new(left.range_adjacent(right)),
            }
        }
        PgBool::RangeHas(value, element) => Box::new(
            PgRangeExpressionMethods::contains(
                range(value).assume_not_null(),
                int(element).assume_not_null(),
            )
            .nullable(),
        ),
        PgBool::InRange(element, value) => Box::new(
            int(element)
                .assume_not_null()
                .is_contained_by_range(range(value).assume_not_null())
                .nullable(),
        ),
        PgBool::Net(op, left, right) => {
            let (left, right) = (net(left), net(right).assume_not_null());
            match op {
                NetOp::Contains => Box::new(PgNetExpressionMethods::contains(left, right)),
                NetOp::ContainsOrEq => Box::new(left.contains_or_eq(right)),
                NetOp::IsContainedBy => {
                    Box::new(PgNetExpressionMethods::is_contained_by(left, right))
                }
                NetOp::IsContainedByOrEq => Box::new(left.is_contained_by_or_eq(right)),
                NetOp::Overlaps => Box::new(PgNetExpressionMethods::overlaps_with(left, right)),
            }
        }
        PgBool::NetDistance(op, left, right, distance) => {
            let difference: Boxed<'_, BigInt> =
                Box::new(net(left).diff(net(right).assume_not_null()));
            compare!(op, difference, distance.into_sql::<Nullable<BigInt>>())
        }
        PgBool::Stamp(op, left, right) => compare!(op, stamp(left), stamp(right)),
        PgBool::StampTz(op, left, right) => compare!(op, stamp_tz(left), stamp_tz(right)),
        PgBool::BinaryMatch {
            negated: false,
            value,
            pattern,
            escape,
        } => escaped!(
            PgBinaryExpressionMethods::like(binary(value), binary(pattern)),
            *escape
        ),
        PgBool::BinaryMatch {
            negated: true,
            value,
            pattern,
            escape,
        } => escaped!(
            PgBinaryExpressionMethods::not_like(binary(value), binary(pattern)),
            *escape
        ),
    }
}

#[derive(Debug, thiserror::Error)]
pub enum Violation {
    #[error("diesel fails with {source} rendering {query:?} for postgres")]
    Render {
        query: String,
        #[source]
        source: diesel::result::Error,
    },
    #[error("postgres rejects the sql diesel built\n  sql: {sql}\n  error: {source}")]
    Rejected {
        sql: String,
        #[source]
        source: pg_query::Error,
    },
    #[error(
        "postgres reads a different operator nesting\n  sql: {sql}\n  meant: {meant}\n  read: {read}"
    )]
    Nesting {
        sql: String,
        meant: Shape,
        read: Shape,
    },
}

/// Renders `query` for postgres, then compares what postgres reads against the tree.
pub fn check(query: &Query) -> Result<(), Violation> {
    compare(render(query)?, query)
}

/// Renders a grouped query for postgres, then compares what postgres reads against the tree.
pub fn check_grouped(tree: &Grouping) -> Result<(), Violation> {
    let mut builder = PgQueryBuilder::new();
    <GroupStatement<'_> as QueryFragment<Pg>>::to_sql(&grouped(tree), &mut builder, &Pg).map_err(
        |source| Violation::Render {
            query: format!("{tree:?}"),
            source,
        },
    )?;
    let sql = builder.finish();
    let parsed = match pg_query::parse(&sql) {
        Ok(parsed) => parsed,
        Err(source) => return Err(Violation::Rejected { sql, source }),
    };
    let read = read_statement(&parsed.protobuf);
    let meant = Expected::default().grouped(tree);
    if read == meant {
        Ok(())
    } else {
        Err(Violation::Nesting { sql, meant, read })
    }
}

/// Parses `sql` with postgres' own grammar and compares the tree it reads against `query`.
pub fn compare(sql: String, query: &Query) -> Result<(), Violation> {
    let parsed = match pg_query::parse(&sql) {
        Ok(parsed) => parsed,
        Err(source) => return Err(Violation::Rejected { sql, source }),
    };
    let read = read_statement(&parsed.protobuf);
    let meant = Expected::default().statement(query);
    if read == meant {
        Ok(())
    } else {
        Err(Violation::Nesting { sql, meant, read })
    }
}

pub fn render(query: &Query) -> Result<String, Violation> {
    let mut builder = PgQueryBuilder::new();
    <Statement<'_> as QueryFragment<Pg>>::to_sql(&statement(query), &mut builder, &Pg).map_err(
        |source| Violation::Render {
            query: format!("{query:?}"),
            source,
        },
    )?;
    Ok(builder.finish())
}

/// An operator tree with parentheses resolved. `AND` and `OR` absorb children of their own kind,
/// since postgres flattens a left nested chain into one node and both operators associate.
#[derive(Debug, PartialEq, Eq)]
pub struct Shape {
    label: String,
    children: Vec<Shape>,
}

impl Shape {
    fn leaf(label: impl Into<String>) -> Self {
        Shape {
            label: label.into(),
            children: Vec::new(),
        }
    }

    fn node(label: impl Into<String>, children: Vec<Shape>) -> Self {
        let label = label.into();
        let children = if label == "AND" || label == "OR" {
            children
                .into_iter()
                .flat_map(|child| {
                    if child.label == label {
                        child.children
                    } else {
                        vec![child]
                    }
                })
                .collect()
        } else {
            children
        };
        Shape { label, children }
    }

    /// An end of `[low:high]` the sql leaves out.
    fn absent() -> Self {
        Shape::leaf("_")
    }
}

impl fmt::Display for Shape {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.children.is_empty() {
            return f.write_str(&self.label);
        }
        write!(f, "({}", self.label)?;
        for child in &self.children {
            write!(f, " {child}")?;
        }
        f.write_str(")")
    }
}

/// The shape postgres should read, with binds numbered in the order diesel renders them.
#[derive(Default)]
struct Expected {
    binds: usize,
}

fn cast(target: &str, value: Shape) -> Shape {
    Shape::node(format!("CAST {target}"), vec![value])
}

impl Expected {
    fn bind(&mut self) -> Shape {
        self.binds += 1;
        Shape::leaf(format!("${}", self.binds))
    }

    fn statement(mut self, query: &Query) -> Shape {
        let mut children = Vec::new();
        if query.distinct {
            children.push(Shape::leaf("DISTINCT"));
        }
        children.extend([
            self.int(&query.int),
            self.text(&query.text),
            self.boolean(&query.bool),
        ]);
        if let Some(filter) = &query.filter {
            children.push(Shape::node("WHERE", vec![self.boolean(filter)]));
        }
        let mut order = vec![Shape::node("SORT", vec![Shape::leaf("t.id")])];
        if let Some(key) = &query.order {
            let direction = if key.descending { "DESC" } else { "ASC" };
            let nulls = match key.nulls {
                None => "",
                Some(Nulls::First) => " NULLS FIRST",
                Some(Nulls::Last) => " NULLS LAST",
            };
            order.push(Shape::node(
                format!("SORT {direction}{nulls}"),
                vec![self.int(&key.key)],
            ));
        }
        children.push(Shape::node("ORDER", order));
        if query.limit.is_some() {
            children.push(Shape::node("LIMIT", vec![self.bind()]));
        }
        if query.offset.is_some() {
            children.push(Shape::node("OFFSET", vec![self.bind()]));
        }
        Shape::node("SELECT", children)
    }

    fn grouped(mut self, tree: &Grouping) -> Shape {
        let mut children = vec![
            Shape::leaf("t.g"),
            self.aggregate_int(&tree.int),
            self.aggregate_big(&tree.big),
        ];
        if let Some(filter) = &tree.filter {
            children.push(Shape::node("WHERE", vec![self.boolean(filter)]));
        }
        children.push(Shape::node("GROUP", vec![Shape::leaf("t.g")]));
        if let Some(having) = &tree.having {
            children.push(Shape::node("HAVING", vec![self.aggregate_bool(having)]));
        }
        children.push(Shape::node(
            "ORDER",
            vec![Shape::node("SORT", vec![Shape::leaf("t.g")])],
        ));
        Shape::node("SELECT", children)
    }

    fn aggregate_int(&mut self, tree: &AggInt) -> Shape {
        match tree {
            AggInt::Key => Shape::leaf("t.g"),
            AggInt::Literal(_) => self.bind(),
            AggInt::Min(value) => Shape::node("min()", vec![self.int(value)]),
            AggInt::Max(value) => Shape::node("max()", vec![self.int(value)]),
            AggInt::Arith(op, left, right) => {
                let op = match op {
                    Arith::Add => "+",
                    Arith::Sub => "-",
                    Arith::Mul => "*",
                    Arith::Div => "/",
                };
                Shape::node(
                    op,
                    vec![self.aggregate_int(left), self.aggregate_int(right)],
                )
            }
        }
    }

    fn aggregate_big(&mut self, tree: &AggBig) -> Shape {
        match tree {
            AggBig::Literal(_) => self.bind(),
            AggBig::Sum(value) => Shape::node("sum()", vec![self.int(value)]),
            AggBig::Count(value) => Shape::node("count()", vec![self.int(value)]),
            AggBig::CountStar => Shape::leaf("count(*)"),
        }
    }

    fn aggregate_bool(&mut self, tree: &AggBool) -> Shape {
        match tree {
            AggBool::Literal(_) => self.bind(),
            AggBool::Compare(op, left, right) => Shape::node(
                comparison(*op),
                vec![self.aggregate_int(left), self.aggregate_int(right)],
            ),
            AggBool::CompareBig(op, left, right) => Shape::node(
                comparison(*op),
                vec![self.aggregate_big(left), self.aggregate_big(right)],
            ),
            AggBool::IsNull { negated, value } => {
                Shape::node(null_test(*negated), vec![self.aggregate_int(value)])
            }
            AggBool::And(left, right) => Shape::node(
                "AND",
                vec![self.aggregate_bool(left), self.aggregate_bool(right)],
            ),
            AggBool::Or(left, right) => Shape::node(
                "OR",
                vec![self.aggregate_bool(left), self.aggregate_bool(right)],
            ),
            AggBool::Not(inner) => Shape::node("NOT", vec![self.aggregate_bool(inner)]),
        }
    }

    /// Diesel's `single_value` limits the subselect to one row, bound like any other value.
    fn subselect(&mut self, tree: &Subquery, limited: bool) -> Shape {
        let mut children = vec![self.int(&tree.select)];
        if let Some(filter) = &tree.filter {
            children.push(Shape::node("WHERE", vec![self.boolean(filter)]));
        }
        children.push(Shape::node(
            "ORDER",
            vec![Shape::node("SORT", vec![Shape::leaf("t.id")])],
        ));
        if limited {
            children.push(Shape::node("LIMIT", vec![self.bind()]));
        }
        Shape::node("SELECT", children)
    }

    fn key(&mut self, key: &JsonKey) -> Shape {
        match key {
            JsonKey::Name(_) | JsonKey::Position(_) => self.bind(),
            JsonKey::Text(tree) => self.text(tree),
            JsonKey::Int(tree) => self.int(tree),
        }
    }

    fn int(&mut self, tree: &Int) -> Shape {
        match tree {
            Int::Column(IntColumn::A) => Shape::leaf("t.a"),
            Int::Column(IntColumn::B) => Shape::leaf("t.b"),
            Int::Column(IntColumn::G) => Shape::leaf("t.g"),
            Int::Literal(_) => self.bind(),
            Int::Arith(op, left, right) => {
                let op = match op {
                    Arith::Add => "+",
                    Arith::Sub => "-",
                    Arith::Mul => "*",
                    Arith::Div => "/",
                };
                Shape::node(op, vec![self.int(left), self.int(right)])
            }
            Int::Case {
                when,
                then,
                second,
                otherwise,
            } => {
                let mut children = vec![Shape::node(
                    "WHEN",
                    vec![self.boolean(when), self.int(then)],
                )];
                if let Some((when, then)) = second {
                    children.push(Shape::node(
                        "WHEN",
                        vec![self.boolean(when), self.int(then)],
                    ));
                }
                if let Some(otherwise) = otherwise {
                    children.push(Shape::node("ELSE", vec![self.int(otherwise)]));
                }
                Shape::node("CASE", children)
            }
            Int::FromText(value) => cast("int4", self.text(value)),
            Int::Scalar(subquery) => Shape::node("SUBQUERY", vec![self.subselect(subquery, true)]),
            Int::Postgres(PgInt::FromBool(value)) => cast("int4", self.boolean(value)),
            Int::Postgres(PgInt::Index(array, index)) => {
                Shape::node("[]", vec![self.ints(array), self.int(index)])
            }
            Int::Postgres(PgInt::IndexLiteral(array, _)) => {
                Shape::node("[]", vec![self.ints(array), self.bind()])
            }
        }
    }

    fn text(&mut self, tree: &Text) -> Shape {
        match tree {
            Text::Column(TextColumn::S) => Shape::leaf("t.s"),
            Text::Column(TextColumn::N) => Shape::leaf("t.n"),
            Text::Literal(_) => self.bind(),
            Text::Concat(left, right) => Shape::node("||", vec![self.text(left), self.text(right)]),
            Text::FromInt(value) => cast("text", self.int(value)),
            Text::FromJson(value) => cast("text", self.json(value)),
            Text::JsonField(value, key) => {
                Shape::node("->>", vec![self.json(value), self.key(key)])
            }
            Text::Postgres(PgText::FromBool(value)) => cast("text", self.boolean(value)),
            Text::Postgres(PgText::FromJsonb(value)) => cast("text", self.jsonb(value)),
            Text::Postgres(PgText::FromNet(value)) => cast("text", self.net(value)),
            Text::Postgres(PgText::JsonbField(value, key)) => {
                Shape::node("->>", vec![self.jsonb(value), self.key(key)])
            }
            Text::Postgres(PgText::JsonbPath(value, _)) => {
                Shape::node("#>>", vec![self.jsonb(value), self.bind()])
            }
        }
    }

    fn json(&mut self, tree: &Json) -> Shape {
        match tree {
            Json::Column => Shape::leaf("t.j"),
            Json::Literal(_) => self.bind(),
            Json::Field(value, key) => Shape::node("->", vec![self.json(value), self.key(key)]),
            Json::FromText(value) => cast("json", self.text(value)),
            Json::Postgres(PgJson::FromJsonb(value)) => cast("json", self.jsonb(value)),
        }
    }

    fn boolean(&mut self, tree: &Bool) -> Shape {
        match tree {
            Bool::Column => Shape::leaf("t.f"),
            Bool::Literal(_) => self.bind(),
            Bool::Compare(op, left, right) => {
                Shape::node(comparison(*op), vec![self.int(left), self.int(right)])
            }
            Bool::CompareText(op, left, right) => {
                Shape::node(comparison(*op), vec![self.text(left), self.text(right)])
            }
            Bool::Between {
                negated,
                value,
                low,
                high,
            } => Shape::node(
                if *negated { "NOT BETWEEN" } else { "BETWEEN" },
                vec![self.int(value), self.int(low), self.int(high)],
            ),
            Bool::In { negated, value, .. } => {
                let value = self.int(value);
                let op = if *negated { "ALL <>" } else { "ANY =" };
                Shape::node(op, vec![value, self.bind()])
            }
            Bool::InSubquery {
                negated,
                value,
                subquery,
            } => {
                let value = self.int(value);
                let op = if *negated { "ALL <>" } else { "ANY =" };
                Shape::node(op, vec![value, self.subselect(subquery, false)])
            }
            Bool::Exists(subquery) => Shape::node("EXISTS", vec![self.subselect(subquery, false)]),
            Bool::IsNull { negated, value } => {
                Shape::node(null_test(*negated), vec![self.int(value)])
            }
            Bool::IsNullText { negated, value } => {
                Shape::node(null_test(*negated), vec![self.text(value)])
            }
            Bool::Distinct {
                negated,
                left,
                right,
            } => Shape::node(
                if *negated {
                    "IS NOT DISTINCT FROM"
                } else {
                    "IS DISTINCT FROM"
                },
                vec![self.int(left), self.int(right)],
            ),
            Bool::Match {
                matcher,
                negated,
                value,
                pattern,
                escape,
            } => {
                let op = match (matcher, negated) {
                    (Matcher::Like, false) => "~~",
                    (Matcher::Like, true) => "!~~",
                    (Matcher::ILike, false) => "~~*",
                    (Matcher::ILike, true) => "!~~*",
                    (Matcher::SimilarTo, false) => "~",
                    (Matcher::SimilarTo, true) => "!~",
                };
                let value = self.text(value);
                let pattern = self.text(pattern);
                let pattern = self.escaped(pattern, *matcher, escape.is_some());
                Shape::node(op, vec![value, pattern])
            }
            Bool::And(left, right) => {
                Shape::node("AND", vec![self.boolean(left), self.boolean(right)])
            }
            Bool::Or(left, right) => {
                Shape::node("OR", vec![self.boolean(left), self.boolean(right)])
            }
            Bool::Not(inner) => Shape::node("NOT", vec![self.boolean(inner)]),
            Bool::Postgres(tree) => self.postgres_bool(tree),
        }
    }

    /// Postgres moves a pattern and its escape into a function call.
    fn escaped(&mut self, pattern: Shape, matcher: Matcher, escape: bool) -> Shape {
        let mut arguments = vec![pattern];
        if escape {
            arguments.push(self.bind());
        }
        match (matcher, escape) {
            (Matcher::SimilarTo, _) => Shape::node("similar_to_escape()", arguments),
            (_, true) => Shape::node("like_escape()", arguments),
            (_, false) => arguments.remove(0),
        }
    }

    fn postgres_bool(&mut self, tree: &PgBool) -> Shape {
        match tree {
            PgBool::FromInt(value) => cast("bool", self.int(value)),
            PgBool::HasKey(value, key) => Shape::node("?", vec![self.jsonb(value), self.text(key)]),
            PgBool::HasAnyKey(value, _) => Shape::node("?|", vec![self.jsonb(value), self.bind()]),
            PgBool::HasAllKeys(value, _) => Shape::node("?&", vec![self.jsonb(value), self.bind()]),
            PgBool::JsonbContains(left, right) => {
                Shape::node("@>", vec![self.jsonb(left), self.jsonb(right)])
            }
            PgBool::JsonbIsContainedBy(left, right) => {
                Shape::node("<@", vec![self.jsonb(left), self.jsonb(right)])
            }
            PgBool::IsJson {
                kind,
                negated,
                value,
            } => {
                let kind = match kind {
                    JsonKind::Any => "IS JSON",
                    JsonKind::Object => "IS JSON OBJECT",
                    JsonKind::Array => "IS JSON ARRAY",
                    JsonKind::Scalar => "IS JSON SCALAR",
                };
                let test = Shape::node(kind, vec![self.text(value)]);
                if *negated {
                    Shape::node("NOT", vec![test])
                } else {
                    test
                }
            }
            PgBool::Array(op, left, right) => {
                let op = match op {
                    ArrayOp::Overlaps => "&&",
                    ArrayOp::Contains => "@>",
                    ArrayOp::IsContainedBy => "<@",
                };
                Shape::node(op, vec![self.ints(left), self.ints(right)])
            }
            PgBool::Range(op, left, right) => {
                let op = match op {
                    RangeOp::Contains => "@>",
                    RangeOp::IsContainedBy => "<@",
                    RangeOp::Overlaps => "&&",
                    RangeOp::ExtendsRightTo => "&<",
                    RangeOp::ExtendsLeftTo => "&>",
                    RangeOp::LesserThan => "<<",
                    RangeOp::GreaterThan => ">>",
                    RangeOp::Adjacent => "-|-",
                };
                Shape::node(op, vec![self.range(left), self.range(right)])
            }
            PgBool::RangeHas(value, element) => {
                Shape::node("@>", vec![self.range(value), self.int(element)])
            }
            PgBool::InRange(element, value) => {
                Shape::node("<@", vec![self.int(element), self.range(value)])
            }
            PgBool::Net(op, left, right) => {
                let op = match op {
                    NetOp::Contains => ">>",
                    NetOp::ContainsOrEq => ">>=",
                    NetOp::IsContainedBy => "<<",
                    NetOp::IsContainedByOrEq => "<<=",
                    NetOp::Overlaps => "&&",
                };
                Shape::node(op, vec![self.net(left), self.net(right)])
            }
            PgBool::NetDistance(op, left, right, _) => {
                let difference = Shape::node("-", vec![self.net(left), self.net(right)]);
                Shape::node(comparison(*op), vec![difference, self.bind()])
            }
            PgBool::Stamp(op, left, right) => {
                Shape::node(comparison(*op), vec![self.stamp(left), self.stamp(right)])
            }
            PgBool::StampTz(op, left, right) => Shape::node(
                comparison(*op),
                vec![self.stamp_tz(left), self.stamp_tz(right)],
            ),
            PgBool::BinaryMatch {
                negated,
                value,
                pattern,
                escape,
            } => {
                let value = self.binary(value);
                let pattern = self.binary(pattern);
                let pattern = self.escaped(pattern, Matcher::Like, escape.is_some());
                Shape::node(if *negated { "!~~" } else { "~~" }, vec![value, pattern])
            }
        }
    }

    fn ints(&mut self, tree: &IntArray) -> Shape {
        match tree {
            IntArray::Column => Shape::leaf("t.ia"),
            IntArray::Literal(_) => self.bind(),
            IntArray::Concat(left, right) => {
                Shape::node("||", vec![self.ints(left), self.ints(right)])
            }
            IntArray::Build(items) => {
                Shape::node("ARRAY[]", items.iter().map(|item| self.int(item)).collect())
            }
            IntArray::FromSubquery(subquery) => {
                Shape::node("ARRAY()", vec![self.subselect(subquery, false)])
            }
            IntArray::Slice(array, bounds) => {
                let array = self.ints(array);
                let (low, high) = match bounds {
                    Bounds::Both(low, high) => (self.int(low), self.int(high)),
                    Bounds::From(low) => (self.int(low), Shape::absent()),
                    Bounds::To(high) => (Shape::absent(), self.int(high)),
                };
                Shape::node("[:]", vec![array, low, high])
            }
            IntArray::SliceLiteral(array, bounds) => {
                let array = self.ints(array);
                let (low, high) = match bounds {
                    Bounds::Both(..) => (self.bind(), self.bind()),
                    Bounds::From(_) => (self.bind(), Shape::absent()),
                    Bounds::To(_) => (Shape::absent(), self.bind()),
                };
                Shape::node("[:]", vec![array, low, high])
            }
        }
    }

    fn jsonb(&mut self, tree: &Jsonb) -> Shape {
        match tree {
            Jsonb::Column => Shape::leaf("t.jb"),
            Jsonb::Literal(_) => self.bind(),
            Jsonb::Concat(left, right) => {
                Shape::node("||", vec![self.jsonb(left), self.jsonb(right)])
            }
            Jsonb::Remove(value, _) => Shape::node("-", vec![self.jsonb(value), self.bind()]),
            Jsonb::RemovePath(value, _) => Shape::node("#-", vec![self.jsonb(value), self.bind()]),
            Jsonb::Field(value, key) => Shape::node("->", vec![self.jsonb(value), self.key(key)]),
            Jsonb::Path(value, _) => Shape::node("#>", vec![self.jsonb(value), self.bind()]),
            Jsonb::FromText(value) => cast("jsonb", self.text(value)),
            Jsonb::FromJson(value) => cast("jsonb", self.json(value)),
        }
    }

    fn range(&mut self, tree: &Range) -> Shape {
        match tree {
            Range::Column => Shape::leaf("t.r"),
            Range::Literal(..) => self.bind(),
            Range::Combine(op, left, right) => {
                let op = match op {
                    RangeCombine::Union => "+",
                    RangeCombine::Difference => "-",
                    RangeCombine::Intersection => "*",
                };
                Shape::node(op, vec![self.range(left), self.range(right)])
            }
        }
    }

    fn net(&mut self, tree: &Net) -> Shape {
        match tree {
            Net::Column => Shape::leaf("t.ip"),
            Net::Literal(_) => self.bind(),
            Net::Mask(op, left, right) => {
                let op = match op {
                    NetMask::And => "&",
                    NetMask::Or => "|",
                };
                Shape::node(op, vec![self.net(left), self.net(right)])
            }
            Net::FromText(value) => cast("inet", self.text(value)),
        }
    }

    /// Postgres reads `x AT TIME ZONE zone` as `timezone(zone, x)`, arguments swapped.
    fn at_zone(instant: Shape, zone: Shape) -> Shape {
        Shape::node("timezone()", vec![zone, instant])
    }

    fn stamp(&mut self, tree: &Stamp) -> Shape {
        match tree {
            Stamp::Column => Shape::leaf("t.ts"),
            Stamp::Literal(_) => self.bind(),
            Stamp::AtZone(instant, zone) => {
                let instant = match instant.as_ref() {
                    Zoned::Stamp(instant) => self.stamp(instant),
                    Zoned::StampTz(instant) => self.stamp_tz(instant),
                };
                Self::at_zone(instant, self.text(zone))
            }
        }
    }

    fn stamp_tz(&mut self, tree: &StampTz) -> Shape {
        match tree {
            StampTz::Column => Shape::leaf("t.tz"),
            StampTz::Literal(_) => self.bind(),
        }
    }

    fn binary(&mut self, tree: &Binary) -> Shape {
        match tree {
            Binary::Column => Shape::leaf("t.bin"),
            Binary::Literal(_) => self.bind(),
            Binary::Concat(left, right) => {
                Shape::node("||", vec![self.binary(left), self.binary(right)])
            }
        }
    }
}

fn comparison(op: Comparison) -> &'static str {
    match op {
        Comparison::Eq => "=",
        Comparison::NotEq => "<>",
        Comparison::Lt => "<",
        Comparison::LtEq => "<=",
        Comparison::Gt => ">",
        Comparison::GtEq => ">=",
    }
}

fn null_test(negated: bool) -> &'static str {
    if negated { "IS NOT NULL" } else { "IS NULL" }
}

fn read_statement(parsed: &pg_query::protobuf::ParseResult) -> Shape {
    let [statement] = parsed.stmts.as_slice() else {
        return Shape::leaf(format!("{} statements", parsed.stmts.len()));
    };
    match statement.stmt.as_ref().and_then(|s| s.node.as_ref()) {
        Some(NodeEnum::SelectStmt(select)) => read_select(select),
        _ => Shape::leaf("not a SELECT"),
    }
}

fn read_select(select: &SelectStmt) -> Shape {
    let mut children = Vec::new();
    if !select.distinct_clause.is_empty() {
        children.push(Shape::leaf("DISTINCT"));
    }
    children.extend(select.target_list.iter().map(|target| match &target.node {
        Some(NodeEnum::ResTarget(target)) => read_boxed(&target.val),
        _ => read(target),
    }));
    if select.where_clause.is_some() {
        children.push(Shape::node("WHERE", vec![read_boxed(&select.where_clause)]));
    }
    if !select.group_clause.is_empty() {
        children.push(Shape::node(
            "GROUP",
            select.group_clause.iter().map(read).collect(),
        ));
    }
    if select.having_clause.is_some() {
        children.push(Shape::node(
            "HAVING",
            vec![read_boxed(&select.having_clause)],
        ));
    }
    if !select.sort_clause.is_empty() {
        children.push(Shape::node(
            "ORDER",
            select.sort_clause.iter().map(read).collect(),
        ));
    }
    if select.limit_count.is_some() {
        children.push(Shape::node("LIMIT", vec![read_boxed(&select.limit_count)]));
    }
    if select.limit_offset.is_some() {
        children.push(Shape::node(
            "OFFSET",
            vec![read_boxed(&select.limit_offset)],
        ));
    }
    Shape::node("SELECT", children)
}

fn read_boxed(node: &Option<Box<Node>>) -> Shape {
    node.as_deref().map_or_else(|| Shape::leaf("missing"), read)
}

fn names(nodes: &[Node]) -> String {
    let names: Vec<&str> = nodes
        .iter()
        .map(|node| match &node.node {
            Some(NodeEnum::String(name)) => name.sval.as_str(),
            _ => "?",
        })
        .collect();
    names.join(".")
}

fn read(node: &Node) -> Shape {
    let Some(node) = &node.node else {
        return Shape::leaf("empty");
    };
    match node {
        NodeEnum::ColumnRef(column) => Shape::leaf(names(&column.fields)),
        NodeEnum::ParamRef(param) => Shape::leaf(format!("${}", param.number)),
        NodeEnum::AExpr(expr) => {
            let name = names(&expr.name);
            let label = match AExprKind::try_from(expr.kind) {
                Ok(AExprKind::AexprOpAny) => format!("ANY {name}"),
                Ok(AExprKind::AexprOpAll) => format!("ALL {name}"),
                Ok(AExprKind::AexprDistinct) => "IS DISTINCT FROM".to_owned(),
                Ok(AExprKind::AexprNotDistinct) => "IS NOT DISTINCT FROM".to_owned(),
                Ok(AExprKind::AexprIn) => format!("IN {name}"),
                Ok(
                    AExprKind::AexprOp
                    | AExprKind::AexprLike
                    | AExprKind::AexprIlike
                    | AExprKind::AexprSimilar
                    | AExprKind::AexprBetween
                    | AExprKind::AexprNotBetween,
                ) => name,
                other => format!("{other:?} {name}"),
            };
            let mut children = Vec::new();
            if expr.lexpr.is_some() {
                children.push(read_boxed(&expr.lexpr));
            }
            match expr.rexpr.as_deref().and_then(|rexpr| rexpr.node.as_ref()) {
                Some(NodeEnum::List(list)) => children.extend(list.items.iter().map(read)),
                _ => children.push(read_boxed(&expr.rexpr)),
            }
            Shape::node(label, children)
        }
        NodeEnum::BoolExpr(expr) => {
            let label = match BoolExprType::try_from(expr.boolop) {
                Ok(BoolExprType::AndExpr) => "AND".to_owned(),
                Ok(BoolExprType::OrExpr) => "OR".to_owned(),
                Ok(BoolExprType::NotExpr) => "NOT".to_owned(),
                other => format!("{other:?}"),
            };
            Shape::node(label, expr.args.iter().map(read).collect())
        }
        NodeEnum::NullTest(test) => {
            let label = match NullTestType::try_from(test.nulltesttype) {
                Ok(NullTestType::IsNull) => "IS NULL".to_owned(),
                Ok(NullTestType::IsNotNull) => "IS NOT NULL".to_owned(),
                other => format!("{other:?}"),
            };
            Shape::node(label, vec![read_boxed(&test.arg)])
        }
        NodeEnum::FuncCall(call) => {
            let name = call
                .funcname
                .last()
                .map_or_else(String::new, |last| names(std::slice::from_ref(last)));
            if call.agg_star {
                return Shape::leaf(format!("{name}(*)"));
            }
            Shape::node(format!("{name}()"), call.args.iter().map(read).collect())
        }
        NodeEnum::CaseExpr(case) => {
            let mut children: Vec<Shape> = case
                .args
                .iter()
                .map(|when| match &when.node {
                    Some(NodeEnum::CaseWhen(when)) => Shape::node(
                        "WHEN",
                        vec![read_boxed(&when.expr), read_boxed(&when.result)],
                    ),
                    _ => read(when),
                })
                .collect();
            if case.defresult.is_some() {
                children.push(Shape::node("ELSE", vec![read_boxed(&case.defresult)]));
            }
            Shape::node("CASE", children)
        }
        NodeEnum::TypeCast(cast) => {
            let target = cast.type_name.as_ref().map_or_else(String::new, |name| {
                name.names
                    .last()
                    .map_or_else(String::new, |last| names(std::slice::from_ref(last)))
            });
            Shape::node(format!("CAST {target}"), vec![read_boxed(&cast.arg)])
        }
        NodeEnum::SubLink(link) => {
            let operator = names(&link.oper_name);
            let label = match SubLinkType::try_from(link.sub_link_type) {
                Ok(SubLinkType::ExistsSublink) => "EXISTS".to_owned(),
                Ok(SubLinkType::AnySublink) if operator.is_empty() => "IN".to_owned(),
                Ok(SubLinkType::AnySublink) => format!("ANY {operator}"),
                Ok(SubLinkType::AllSublink) => format!("ALL {operator}"),
                Ok(SubLinkType::ExprSublink) => "SUBQUERY".to_owned(),
                Ok(SubLinkType::ArraySublink) => "ARRAY()".to_owned(),
                other => format!("{other:?}"),
            };
            let mut children = Vec::new();
            if link.testexpr.is_some() {
                children.push(read_boxed(&link.testexpr));
            }
            children.push(
                match link.subselect.as_deref().and_then(|s| s.node.as_ref()) {
                    Some(NodeEnum::SelectStmt(select)) => read_select(select),
                    _ => read_boxed(&link.subselect),
                },
            );
            Shape::node(label, children)
        }
        NodeEnum::AIndirection(indirection) => {
            indirection
                .indirection
                .iter()
                .fold(read_boxed(&indirection.arg), |value, step| {
                    match &step.node {
                        Some(NodeEnum::AIndices(indices)) if indices.is_slice => {
                            let end = |end: &Option<Box<Node>>| {
                                end.as_deref().map_or_else(Shape::absent, read)
                            };
                            Shape::node("[:]", vec![value, end(&indices.lidx), end(&indices.uidx)])
                        }
                        Some(NodeEnum::AIndices(indices)) => {
                            Shape::node("[]", vec![value, read_boxed(&indices.uidx)])
                        }
                        _ => Shape::node("indirection", vec![value, read(step)]),
                    }
                })
        }
        NodeEnum::AArrayExpr(array) => {
            Shape::node("ARRAY[]", array.elements.iter().map(read).collect())
        }
        NodeEnum::JsonIsPredicate(predicate) => {
            let label = match JsonValueType::try_from(predicate.item_type) {
                Ok(JsonValueType::JsTypeAny) => "IS JSON".to_owned(),
                Ok(JsonValueType::JsTypeObject) => "IS JSON OBJECT".to_owned(),
                Ok(JsonValueType::JsTypeArray) => "IS JSON ARRAY".to_owned(),
                Ok(JsonValueType::JsTypeScalar) => "IS JSON SCALAR".to_owned(),
                other => format!("IS JSON {other:?}"),
            };
            Shape::node(label, vec![read_boxed(&predicate.expr)])
        }
        NodeEnum::SortBy(sort) => {
            let direction = match SortByDir::try_from(sort.sortby_dir) {
                Ok(SortByDir::SortbyDefault) => "SORT".to_owned(),
                Ok(SortByDir::SortbyAsc) => "SORT ASC".to_owned(),
                Ok(SortByDir::SortbyDesc) => "SORT DESC".to_owned(),
                other => format!("SORT {other:?}"),
            };
            let nulls = match SortByNulls::try_from(sort.sortby_nulls) {
                Ok(SortByNulls::SortbyNullsDefault) => "",
                Ok(SortByNulls::SortbyNullsFirst) => " NULLS FIRST",
                Ok(SortByNulls::SortbyNullsLast) => " NULLS LAST",
                _ => " NULLS ?",
            };
            Shape::node(format!("{direction}{nulls}"), vec![read_boxed(&sort.node)])
        }
        other => {
            let debug = format!("{other:?}");
            let kind = debug.split('(').next().unwrap_or_default();
            Shape::leaf(format!("unmapped {kind}"))
        }
    }
}
