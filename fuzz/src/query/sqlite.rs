//! Sqlite runs the sql diesel renders next to a fully parenthesised rendering of the same tree,
//! and both must answer alike over the same rows.
//!
//! The reference binds every value diesel binds, in the same order and as the same sql type, so
//! both statements evaluate alike and only the parentheses differ.

use super::{
    AggBig, AggBool, AggInt, Arith, Bool, Comparison, Grouping, Int, IntColumn, Json, JsonKey,
    Order, Query, Subquery, Text, TextColumn, t,
};
use diesel::connection::{CacheSize, SimpleConnection};
use diesel::dsl::{case_when, count, count_star, exists, max, min, not, sum};
use diesel::expression::TypedExpressionType;
use diesel::expression::{
    AppearsOnTable, BoxableExpression, Expression, SelectableExpression, ValidGrouping,
    is_aggregate,
};
use diesel::prelude::*;
use diesel::query_builder::{AstPass, QueryFragment, QueryId};
use diesel::sql_types::{
    BigInt, Bool as SqlBool, Integer, Json as SqlJson, Nullable, Text as SqlText,
};
use diesel::sqlite::Sqlite;
use serde_json::Value;
use std::cell::RefCell;
use std::marker::PhantomData;

pub type Boxed<'a, ST> = Box<dyn BoxableExpression<t::table, Sqlite, SqlType = Nullable<ST>> + 'a>;

pub type Statement<'a> =
    t::BoxedQuery<'a, Sqlite, (Nullable<Integer>, Nullable<SqlText>, Nullable<SqlBool>)>;

pub type Subselect<'a> = t::BoxedQuery<'a, Sqlite, Nullable<Integer>>;

/// An expression of a query grouped by `t.g`, which may aggregate.
pub type Aggregate<'a, ST> = Box<
    dyn BoxableExpression<t::table, Sqlite, t::g, is_aggregate::Yes, SqlType = Nullable<ST>> + 'a,
>;

pub type GroupStatement<'a> = diesel::dsl::IntoBoxed<
    'a,
    diesel::dsl::Select<
        diesel::dsl::GroupBy<t::table, t::g>,
        (t::g, Aggregate<'a, Integer>, Aggregate<'a, BigInt>),
    >,
    Sqlite,
>;

/// A boxed aggregate integer, which unlike the box itself takes `+`, `-`, `*` and `/`.
#[derive(diesel::sql_types::DieselNumericOps)]
pub struct AggNumber<'a>(Aggregate<'a, Integer>);

impl Expression for AggNumber<'_> {
    type SqlType = Nullable<Integer>;
}

impl QueryFragment<Sqlite> for AggNumber<'_> {
    fn walk_ast<'b>(&'b self, pass: AstPass<'_, 'b, Sqlite>) -> QueryResult<()> {
        self.0.walk_ast(pass)
    }
}

impl QueryId for AggNumber<'_> {
    type QueryId = ();
    const HAS_STATIC_QUERY_ID: bool = false;
}

impl ValidGrouping<t::g> for AggNumber<'_> {
    type IsAggregate = is_aggregate::Yes;
}

impl AppearsOnTable<t::table> for AggNumber<'_> {}

impl SelectableExpression<t::table> for AggNumber<'_> {}

/// A boxed integer, which unlike the box itself takes `+`, `-`, `*` and `/`.
#[derive(diesel::sql_types::DieselNumericOps)]
pub struct Number<'a>(Boxed<'a, Integer>);

impl Expression for Number<'_> {
    type SqlType = Nullable<Integer>;
}

impl QueryFragment<Sqlite> for Number<'_> {
    fn walk_ast<'b>(&'b self, pass: AstPass<'_, 'b, Sqlite>) -> QueryResult<()> {
        self.0.walk_ast(pass)
    }
}

impl QueryId for Number<'_> {
    type QueryId = ();
    const HAS_STATIC_QUERY_ID: bool = false;
}

impl ValidGrouping<()> for Number<'_> {
    type IsAggregate = is_aggregate::No;
}

impl AppearsOnTable<t::table> for Number<'_> {}

impl SelectableExpression<t::table> for Number<'_> {}

/// Runs `$body` once with `$key` bound to whichever key diesel receives, a bound name,
/// a bound position, or an expression that is not null.
macro_rules! keyed {
    ($tree:expr, |$key:ident| $body:expr) => {
        match $tree {
            JsonKey::Name(name) => {
                let $key = name.as_str();
                $body
            }
            JsonKey::Position(position) => {
                let $key = *position;
                $body
            }
            JsonKey::Text(tree) => {
                let $key = text(tree).assume_not_null();
                $body
            }
            JsonKey::Int(tree) => {
                let $key = int(tree).assume_not_null();
                $body
            }
        }
    };
}

pub fn statement(query: &Query) -> Statement<'_> {
    let statement = t::table
        .select((int(&query.int), text(&query.text), boolean(&query.bool)))
        .order(t::id)
        .into_boxed();
    let statement = match &query.filter {
        Some(filter) => statement.filter(boolean(filter)),
        None => statement,
    };
    let statement = if query.distinct {
        statement.distinct()
    } else {
        statement
    };
    let statement = match query.limit {
        Some(limit) => statement.limit(limit),
        None => statement,
    };
    let statement = match query.offset {
        Some(offset) => statement.offset(offset),
        None => statement,
    };
    match &query.order {
        None => statement,
        Some(Order {
            key,
            descending: false,
        }) => statement.then_order_by(int(key).asc()),
        Some(Order {
            key,
            descending: true,
        }) => statement.then_order_by(int(key).desc()),
    }
}

pub fn grouped(tree: &Grouping) -> GroupStatement<'_> {
    let statement = t::table
        .group_by(t::g)
        .select((t::g, aggregate_int(&tree.int), aggregate_big(&tree.big)))
        .into_boxed()
        .order(t::g);
    let statement = match &tree.filter {
        Some(filter) => statement.filter(boolean(filter)),
        None => statement,
    };
    match &tree.having {
        Some(having) => statement.having(aggregate_bool(having)),
        None => statement,
    }
}

pub fn aggregate_int(tree: &AggInt) -> Aggregate<'_, Integer> {
    match tree {
        AggInt::Key => Box::new(t::g),
        AggInt::Literal(value) => Box::new(value.into_sql::<Nullable<Integer>>()),
        AggInt::Min(value) => Box::new(min(int(value))),
        AggInt::Max(value) => Box::new(max(int(value))),
        AggInt::Arith(op, left, right) => {
            let (left, right) = (
                AggNumber(aggregate_int(left)),
                AggNumber(aggregate_int(right)),
            );
            match op {
                Arith::Add => Box::new(left + right),
                Arith::Sub => Box::new(left - right),
                Arith::Mul => Box::new(left * right),
                Arith::Div => Box::new(left / right),
            }
        }
    }
}

pub fn aggregate_big(tree: &AggBig) -> Aggregate<'_, BigInt> {
    match tree {
        AggBig::Literal(value) => Box::new(value.into_sql::<Nullable<BigInt>>()),
        AggBig::Sum(value) => Box::new(sum(int(value))),
        AggBig::Count(value) => Box::new(count(int(value)).nullable()),
        AggBig::CountStar => Box::new(count_star().nullable()),
    }
}

pub fn aggregate_bool(tree: &AggBool) -> Aggregate<'_, SqlBool> {
    macro_rules! compare_aggregates {
        ($op:expr, $left:expr, $right:expr) => {{
            let (left, right) = ($left, $right);
            let compared: Aggregate<'_, SqlBool> = match $op {
                Comparison::Eq => Box::new(left.eq(right)),
                Comparison::NotEq => Box::new(left.ne(right)),
                Comparison::Lt => Box::new(left.lt(right)),
                Comparison::LtEq => Box::new(left.le(right)),
                Comparison::Gt => Box::new(left.gt(right)),
                Comparison::GtEq => Box::new(left.ge(right)),
            };
            compared
        }};
    }
    match tree {
        AggBool::Literal(value) => Box::new(value.into_sql::<Nullable<SqlBool>>()),
        AggBool::Compare(op, left, right) => {
            compare_aggregates!(op, aggregate_int(left), aggregate_int(right))
        }
        AggBool::CompareBig(op, left, right) => {
            compare_aggregates!(op, aggregate_big(left), aggregate_big(right))
        }
        AggBool::IsNull {
            negated: false,
            value,
        } => Box::new(aggregate_int(value).is_null().nullable()),
        AggBool::IsNull {
            negated: true,
            value,
        } => Box::new(aggregate_int(value).is_not_null().nullable()),
        AggBool::And(left, right) => Box::new(aggregate_bool(left).and(aggregate_bool(right))),
        AggBool::Or(left, right) => Box::new(aggregate_bool(left).or(aggregate_bool(right))),
        AggBool::Not(inner) => Box::new(not(aggregate_bool(inner))),
    }
}

pub fn subselect(tree: &Subquery) -> Subselect<'_> {
    let subselect = t::table.select(int(&tree.select)).order(t::id).into_boxed();
    match &tree.filter {
        Some(filter) => subselect.filter(boolean(filter)),
        None => subselect,
    }
}

pub fn int(tree: &Int) -> Boxed<'_, Integer> {
    match tree {
        Int::Column(IntColumn::A) => Box::new(t::a.nullable()),
        Int::Column(IntColumn::B) => Box::new(t::b),
        Int::Column(IntColumn::G) => Box::new(t::g),
        Int::Literal(value) => Box::new(value.into_sql::<Nullable<Integer>>()),
        Int::Arith(op, left, right) => {
            let (left, right) = (Number(int(left)), Number(int(right)));
            match op {
                Arith::Add => Box::new(left + right),
                Arith::Sub => Box::new(left - right),
                Arith::Mul => Box::new(left * right),
                Arith::Div => Box::new(left / right),
            }
        }
        Int::Case {
            when,
            then,
            second,
            otherwise,
        } => {
            let first = case_when::<_, _, Nullable<Integer>>(boolean(when), int(then));
            match (second, otherwise) {
                (None, None) => Box::new(first),
                (None, Some(otherwise)) => Box::new(first.otherwise(int(otherwise))),
                (Some((when, then)), None) => Box::new(first.when(boolean(when), int(then))),
                (Some((when, then)), Some(otherwise)) => Box::new(
                    first
                        .when(boolean(when), int(then))
                        .otherwise(int(otherwise)),
                ),
            }
        }
        Int::FromText(value) => Box::new(text(value).fallible_cast::<Nullable<Integer>>()),
        Int::Scalar(subquery) => Box::new(subselect(subquery).single_value()),
    }
}

pub fn text(tree: &Text) -> Boxed<'_, SqlText> {
    match tree {
        Text::Column(TextColumn::S) => Box::new(t::s.nullable()),
        Text::Column(TextColumn::N) => Box::new(t::n),
        Text::Literal(value) => Box::new(value.as_str().into_sql::<Nullable<SqlText>>()),
        Text::Concat(left, right) => Box::new(text(left).concat(text(right))),
        Text::FromInt(value) => Box::new(int(value).cast::<Nullable<SqlText>>()),
        Text::FromJson(value) => Box::new(json(value).cast::<Nullable<SqlText>>()),
        Text::JsonField(value, key) => {
            keyed!(key, |key| Box::new(json(value).retrieve_as_text(key)))
        }
    }
}

pub fn json(tree: &Json) -> Boxed<'_, SqlJson> {
    match tree {
        Json::Column => Box::new(t::j),
        Json::Literal(value) => Box::new(value.into_sql::<Nullable<SqlJson>>()),
        Json::Field(value, key) => {
            keyed!(key, |key| Box::new(
                json(value).retrieve_as_object_sqlite(key)
            ))
        }
        Json::FromText(value) => Box::new(text(value).fallible_cast::<Nullable<SqlJson>>()),
    }
}

macro_rules! compare {
    ($op:expr, $left:expr, $right:expr) => {{
        let (left, right) = ($left, $right);
        let compared: Boxed<'_, SqlBool> = match $op {
            Comparison::Eq => Box::new(left.eq(right)),
            Comparison::NotEq => Box::new(left.ne(right)),
            Comparison::Lt => Box::new(left.lt(right)),
            Comparison::LtEq => Box::new(left.le(right)),
            Comparison::Gt => Box::new(left.gt(right)),
            Comparison::GtEq => Box::new(left.ge(right)),
        };
        compared
    }};
}

pub fn boolean(tree: &Bool) -> Boxed<'_, SqlBool> {
    match tree {
        Bool::Column => Box::new(t::f.nullable()),
        Bool::Literal(value) => Box::new(value.into_sql::<Nullable<SqlBool>>()),
        Bool::Compare(op, left, right) => compare!(op, int(left), int(right)),
        Bool::CompareText(op, left, right) => compare!(op, text(left), text(right)),
        Bool::Between {
            negated: false,
            value,
            low,
            high,
        } => Box::new(int(value).between(int(low), int(high))),
        Bool::Between {
            negated: true,
            value,
            low,
            high,
        } => Box::new(int(value).not_between(int(low), int(high))),
        Bool::In {
            negated: false,
            value,
            list,
        } => Box::new(int(value).eq_any(list)),
        Bool::In {
            negated: true,
            value,
            list,
        } => Box::new(int(value).ne_all(list)),
        Bool::InSubquery {
            negated: false,
            value,
            subquery,
        } => Box::new(int(value).eq_any(subselect(subquery))),
        Bool::InSubquery {
            negated: true,
            value,
            subquery,
        } => Box::new(int(value).ne_all(subselect(subquery))),
        Bool::Exists(subquery) => Box::new(exists(subselect(subquery)).nullable()),
        Bool::IsNull {
            negated: false,
            value,
        } => Box::new(int(value).is_null().nullable()),
        Bool::IsNull {
            negated: true,
            value,
        } => Box::new(int(value).is_not_null().nullable()),
        Bool::IsNullText {
            negated: false,
            value,
        } => Box::new(text(value).is_null().nullable()),
        Bool::IsNullText {
            negated: true,
            value,
        } => Box::new(text(value).is_not_null().nullable()),
        Bool::Distinct {
            negated: false,
            left,
            right,
        } => Box::new(int(left).is_not(int(right)).nullable()),
        Bool::Distinct {
            negated: true,
            left,
            right,
        } => Box::new(int(left).is(int(right)).nullable()),
        Bool::Match {
            negated,
            value,
            pattern,
            escape,
        } => {
            let (value, pattern) = (text(value), text(pattern));
            match (negated, escape) {
                (false, None) => Box::new(value.like(pattern)),
                (false, Some(character)) => Box::new(value.like(pattern).escape(*character)),
                (true, None) => Box::new(value.not_like(pattern)),
                (true, Some(character)) => Box::new(value.not_like(pattern).escape(*character)),
            }
        }
        Bool::And(left, right) => Box::new(boolean(left).and(boolean(right))),
        Bool::Or(left, right) => Box::new(boolean(left).or(boolean(right))),
        Bool::Not(inner) => Box::new(not(boolean(inner))),
    }
}

const ROWS: &str = r#"
    CREATE TABLE t (
        id INTEGER PRIMARY KEY,
        a INTEGER NOT NULL,
        b INTEGER,
        s TEXT NOT NULL,
        n TEXT,
        f BOOLEAN NOT NULL,
        g INTEGER,
        j TEXT
    );
    INSERT INTO t VALUES
        (1, 0, NULL, '', NULL, 0, 1, NULL),
        (2, 1, 2, 'a%b', 'A_b', 1, 2, '{"a":1,"b":[1,2]}'),
        (3, -3, 7, 'abc', 'x', 1, 1, '[1,"x",null]'),
        (4, 7, 0, '_%\', '', 0, NULL, '"s"'),
        (5, -2147483648, -1, 'ß', 'SS', 1, 2, '3');
"#;

thread_local! {
    static CONN: RefCell<SqliteConnection> = RefCell::new({
        let mut conn =
            SqliteConnection::establish(":memory:").expect("an in-memory sqlite database");
        conn.batch_execute(ROWS).expect("the fixture rows");
        // every input is new sql, which the statement cache would keep until memory runs out
        conn.set_prepared_statement_cache_size(CacheSize::Disabled);
        conn
    });
}

type Row = (Option<i32>, Option<String>, Option<bool>);

/// Rows, or the message of the error sqlite raised instead.
pub type Answer = Result<Vec<Row>, String>;

type Group = (Option<i32>, Option<i32>, Option<i64>);

#[derive(Debug, thiserror::Error)]
#[error(
    "sqlite answers the sql diesel built differently from the fully parenthesised tree\n  diesel: {built}\n  answer: {built_answer}\n  meant: {meant}\n  answer: {meant_answer}"
)]
pub struct Divergence {
    pub built: String,
    pub built_answer: String,
    pub meant: String,
    pub meant_answer: String,
}

/// Runs the statement diesel builds for `query` and the reference rendering of the same tree.
/// Equal errors pass, since then sqlite refused the expression rather than diesel's spelling.
pub fn check(query: &Query) -> Result<(), Divergence> {
    CONN.with(|conn| {
        let conn = &mut *conn.borrow_mut();
        let mut built_answer: Answer = statement(query).load(conn).map_err(|e| e.to_string());
        let mut meant_answer: Answer = reference(query).load(conn).map_err(|e| e.to_string());
        // `DISTINCT` keeps an arbitrary row of each duplicate, so only the set of rows is fixed
        if query.distinct {
            for rows in [&mut built_answer, &mut meant_answer].into_iter().flatten() {
                rows.sort();
            }
        }
        if built_answer == meant_answer {
            Ok(())
        } else {
            Err(Divergence {
                built: diesel::debug_query::<Sqlite, _>(&statement(query)).to_string(),
                built_answer: format!("{built_answer:?}"),
                meant: diesel::debug_query::<Sqlite, _>(&reference(query)).to_string(),
                meant_answer: format!("{meant_answer:?}"),
            })
        }
    })
}

/// [`check`] for a grouped query.
pub fn check_grouped(tree: &Grouping) -> Result<(), Divergence> {
    CONN.with(|conn| {
        let conn = &mut *conn.borrow_mut();
        let built_answer: Result<Vec<Group>, String> =
            grouped(tree).load(conn).map_err(|e| e.to_string());
        let meant_answer: Result<Vec<Group>, String> = reference_grouped(tree)
            .load(conn)
            .map_err(|e| e.to_string());
        if built_answer == meant_answer {
            Ok(())
        } else {
            Err(Divergence {
                built: diesel::debug_query::<Sqlite, _>(&grouped(tree)).to_string(),
                built_answer: format!("{built_answer:?}"),
                meant: diesel::debug_query::<Sqlite, _>(&reference_grouped(tree)).to_string(),
                meant_answer: format!("{meant_answer:?}"),
            })
        }
    })
}

/// The grouped statement diesel builds, with every expression swapped for its hand written
/// rendering.
fn reference_grouped(tree: &Grouping) -> GroupStatement<'_> {
    let int: Aggregate<'_, Integer> =
        Box::new(Written::new(|out| written::aggregate_int(&tree.int, out)));
    let big: Aggregate<'_, BigInt> =
        Box::new(Written::new(|out| written::aggregate_big(&tree.big, out)));
    let statement = t::table
        .group_by(t::g)
        .select((t::g, int, big))
        .into_boxed()
        .order(t::g);
    let statement = match &tree.filter {
        Some(filter) => statement.filter(Written::<Nullable<SqlBool>>::new(|out| {
            written::boolean(filter, out)
        })),
        None => statement,
    };
    match &tree.having {
        Some(having) => statement.having(Written::<Nullable<SqlBool>>::new(|out| {
            written::aggregate_bool(having, out)
        })),
        None => statement,
    }
}

/// The statement diesel builds, with every expression swapped for its hand written rendering.
fn reference(query: &Query) -> Statement<'_> {
    let statement = t::table
        .select((
            Written::new(|out| written::int(&query.int, out)),
            Written::new(|out| written::text(&query.text, out)),
            Written::new(|out| written::boolean(&query.bool, out)),
        ))
        .order(t::id)
        .into_boxed();
    let statement = match &query.filter {
        Some(filter) => statement.filter(Written::<Nullable<SqlBool>>::new(|out| {
            written::boolean(filter, out)
        })),
        None => statement,
    };
    let statement = if query.distinct {
        statement.distinct()
    } else {
        statement
    };
    let statement = match query.limit {
        Some(limit) => statement.limit(limit),
        None => statement,
    };
    let statement = match query.offset {
        Some(offset) => statement.offset(offset),
        None => statement,
    };
    match &query.order {
        None => statement,
        Some(order) => {
            let key = Written::<Nullable<Integer>>::new(|out| written::int(&order.key, out));
            if order.descending {
                statement.then_order_by(key.desc())
            } else {
                statement.then_order_by(key.asc())
            }
        }
    }
}

/// A value the reference binds, as the sql type diesel binds it as.
enum Bind<'q> {
    Int(i32),
    BigInt(i64),
    Text(&'q str),
    Character(String),
    Bool(bool),
    Json(&'q Value),
}

enum Part<'q> {
    Sql(String),
    Bind(Bind<'q>),
}

/// Hand written sql with its binds in place.
#[derive(Default)]
struct Sink<'q> {
    parts: Vec<Part<'q>>,
}

impl<'q> Sink<'q> {
    fn sql(&mut self, sql: &str) {
        match self.parts.last_mut() {
            Some(Part::Sql(last)) => last.push_str(sql),
            _ => self.parts.push(Part::Sql(sql.to_owned())),
        }
    }

    fn bind(&mut self, value: Bind<'q>) {
        self.parts.push(Part::Bind(value));
    }
}

/// Hand written sql of sql type `ST`.
struct Written<'q, ST> {
    parts: Vec<Part<'q>>,
    sql_type: PhantomData<ST>,
}

impl<'q, ST> Written<'q, ST> {
    fn new(write: impl FnOnce(&mut Sink<'q>)) -> Self {
        let mut sink = Sink::default();
        write(&mut sink);
        Written {
            parts: sink.parts,
            sql_type: PhantomData,
        }
    }
}

impl<ST: TypedExpressionType> Expression for Written<'_, ST> {
    type SqlType = ST;
}

impl<ST> QueryFragment<Sqlite> for Written<'_, ST> {
    fn walk_ast<'b>(&'b self, mut out: AstPass<'_, 'b, Sqlite>) -> QueryResult<()> {
        for part in &self.parts {
            match part {
                Part::Sql(sql) => out.push_sql(sql),
                Part::Bind(Bind::Int(value)) => out.push_bind_param::<Integer, _>(value)?,
                Part::Bind(Bind::BigInt(value)) => out.push_bind_param::<BigInt, _>(value)?,
                Part::Bind(Bind::Text(value)) => out.push_bind_param::<SqlText, str>(*value)?,
                Part::Bind(Bind::Character(value)) => {
                    out.push_bind_param::<SqlText, String>(value)?
                }
                Part::Bind(Bind::Bool(value)) => out.push_bind_param::<SqlBool, _>(value)?,
                Part::Bind(Bind::Json(value)) => out.push_bind_param::<SqlJson, Value>(*value)?,
            }
        }
        Ok(())
    }
}

impl<ST> QueryId for Written<'_, ST> {
    type QueryId = ();
    const HAS_STATIC_QUERY_ID: bool = false;
}

/// Hand written sql may or may not aggregate, like `diesel::dsl::sql`.
impl<ST, GB> ValidGrouping<GB> for Written<'_, ST> {
    type IsAggregate = is_aggregate::Never;
}

impl<ST: TypedExpressionType> AppearsOnTable<t::table> for Written<'_, ST> {}

impl<ST: TypedExpressionType> SelectableExpression<t::table> for Written<'_, ST> {}

/// The tree rendered by hand, every operator in its own parentheses.
mod written {
    use super::super::{
        AggBig, AggBool, AggInt, Arith, Bool, Comparison, Int, IntColumn, Json, JsonKey, Subquery,
        Text, TextColumn,
    };
    use super::{Bind, Sink};

    type Out<'o, 'q> = &'o mut Sink<'q>;

    pub(super) use {write_bool as boolean, write_int as int, write_text as text};

    fn binary<'q>(
        out: Out<'_, 'q>,
        left: impl FnOnce(Out<'_, 'q>),
        op: &str,
        right: impl FnOnce(Out<'_, 'q>),
    ) {
        out.sql("(");
        left(out);
        out.sql(op);
        right(out);
        out.sql(")");
    }

    fn cast<'q>(out: Out<'_, 'q>, value: impl FnOnce(Out<'_, 'q>), target: &str) {
        out.sql("CAST(");
        value(out);
        out.sql(" AS ");
        out.sql(target);
        out.sql(")");
    }

    fn subquery<'q>(tree: &'q Subquery, out: Out<'_, 'q>, limited: bool) {
        out.sql("(SELECT ");
        write_int(&tree.select, out);
        out.sql(" FROM t");
        if let Some(filter) = &tree.filter {
            out.sql(" WHERE ");
            write_bool(filter, out);
        }
        out.sql(" ORDER BY t.id");
        if limited {
            out.sql(" LIMIT ");
            out.bind(Bind::BigInt(1));
        }
        out.sql(")");
    }

    fn key<'q>(tree: &'q JsonKey, out: Out<'_, 'q>) {
        match tree {
            JsonKey::Name(name) => out.bind(Bind::Text(name)),
            JsonKey::Position(position) => out.bind(Bind::Int(*position)),
            JsonKey::Text(tree) => write_text(tree, out),
            JsonKey::Int(tree) => write_int(tree, out),
        }
    }

    pub(super) fn write_int<'q>(tree: &'q Int, out: Out<'_, 'q>) {
        match tree {
            Int::Column(IntColumn::A) => out.sql("t.a"),
            Int::Column(IntColumn::B) => out.sql("t.b"),
            Int::Column(IntColumn::G) => out.sql("t.g"),
            Int::Literal(value) => out.bind(Bind::Int(*value)),
            Int::Arith(op, left, right) => {
                let op = match op {
                    Arith::Add => " + ",
                    Arith::Sub => " - ",
                    Arith::Mul => " * ",
                    Arith::Div => " / ",
                };
                binary(
                    out,
                    |out| write_int(left, out),
                    op,
                    |out| write_int(right, out),
                );
            }
            Int::Case {
                when,
                then,
                second,
                otherwise,
            } => {
                out.sql("(CASE");
                for (when, then) in
                    std::iter::once((when, then)).chain(second.as_ref().map(|(w, t)| (w, t)))
                {
                    out.sql(" WHEN ");
                    write_bool(when, out);
                    out.sql(" THEN ");
                    write_int(then, out);
                }
                if let Some(otherwise) = otherwise {
                    out.sql(" ELSE ");
                    write_int(otherwise, out);
                }
                out.sql(" END)");
            }
            Int::FromText(value) => cast(out, |out| write_text(value, out), "integer"),
            Int::Scalar(tree) => subquery(tree, out, true),
        }
    }

    pub(super) fn write_text<'q>(tree: &'q Text, out: Out<'_, 'q>) {
        match tree {
            Text::Column(TextColumn::S) => out.sql("t.s"),
            Text::Column(TextColumn::N) => out.sql("t.n"),
            Text::Literal(value) => out.bind(Bind::Text(value)),
            Text::Concat(left, right) => {
                binary(
                    out,
                    |out| write_text(left, out),
                    " || ",
                    |out| write_text(right, out),
                );
            }
            Text::FromInt(value) => cast(out, |out| write_int(value, out), "text"),
            Text::FromJson(value) => cast(out, |out| write_json(value, out), "text"),
            Text::JsonField(value, field) => {
                binary(
                    out,
                    |out| write_json(value, out),
                    " ->> ",
                    |out| key(field, out),
                );
            }
        }
    }

    fn write_json<'q>(tree: &'q Json, out: Out<'_, 'q>) {
        match tree {
            Json::Column => out.sql("t.j"),
            Json::Literal(value) => out.bind(Bind::Json(value)),
            Json::Field(value, field) => {
                binary(
                    out,
                    |out| write_json(value, out),
                    " -> ",
                    |out| key(field, out),
                );
            }
            Json::FromText(value) => cast(out, |out| write_text(value, out), "json"),
        }
    }

    pub(super) fn write_bool<'q>(tree: &'q Bool, out: Out<'_, 'q>) {
        match tree {
            Bool::Column => out.sql("t.f"),
            Bool::Literal(value) => out.bind(Bind::Bool(*value)),
            Bool::Compare(op, left, right) => binary(
                out,
                |out| write_int(left, out),
                comparison(*op),
                |out| write_int(right, out),
            ),
            Bool::CompareText(op, left, right) => binary(
                out,
                |out| write_text(left, out),
                comparison(*op),
                |out| write_text(right, out),
            ),
            Bool::Between {
                negated,
                value,
                low,
                high,
            } => {
                out.sql("(");
                write_int(value, out);
                out.sql(if *negated {
                    " NOT BETWEEN "
                } else {
                    " BETWEEN "
                });
                write_int(low, out);
                out.sql(" AND ");
                write_int(high, out);
                out.sql(")");
            }
            // mirrors diesel's rewrite of an empty list into a constant that drops the left
            // operand, since sqlite folds that constant and skips whatever it guards. Neither
            // oracle checks the truth of `x IN ()` because of it
            Bool::In { negated, list, .. } if list.is_empty() => {
                out.sql(if *negated { "1=1" } else { "1=0" });
            }
            Bool::In {
                negated,
                value,
                list,
            } => {
                out.sql("(");
                write_int(value, out);
                out.sql(if *negated { " NOT IN (" } else { " IN (" });
                for (i, item) in list.iter().enumerate() {
                    if i > 0 {
                        out.sql(", ");
                    }
                    out.bind(Bind::Int(*item));
                }
                out.sql("))");
            }
            Bool::InSubquery {
                negated,
                value,
                subquery: tree,
            } => {
                out.sql("(");
                write_int(value, out);
                out.sql(if *negated { " NOT IN " } else { " IN " });
                subquery(tree, out, false);
                out.sql(")");
            }
            Bool::Exists(tree) => {
                out.sql("(EXISTS ");
                subquery(tree, out, false);
                out.sql(")");
            }
            Bool::IsNull { negated, value } => {
                out.sql("(");
                write_int(value, out);
                out.sql(null_test(*negated));
            }
            Bool::IsNullText { negated, value } => {
                out.sql("(");
                write_text(value, out);
                out.sql(null_test(*negated));
            }
            Bool::Distinct {
                negated,
                left,
                right,
            } => {
                let op = if *negated { " IS " } else { " IS NOT " };
                binary(
                    out,
                    |out| write_int(left, out),
                    op,
                    |out| write_int(right, out),
                );
            }
            Bool::Match {
                negated,
                value,
                pattern,
                escape,
            } => {
                out.sql("(");
                write_text(value, out);
                out.sql(if *negated { " NOT LIKE " } else { " LIKE " });
                write_text(pattern, out);
                if let Some(character) = escape {
                    out.sql(" ESCAPE ");
                    out.bind(Bind::Character(character.to_string()));
                }
                out.sql(")");
            }
            Bool::And(left, right) => binary(
                out,
                |out| write_bool(left, out),
                " AND ",
                |out| write_bool(right, out),
            ),
            Bool::Or(left, right) => binary(
                out,
                |out| write_bool(left, out),
                " OR ",
                |out| write_bool(right, out),
            ),
            Bool::Not(inner) => {
                out.sql("(NOT ");
                write_bool(inner, out);
                out.sql(")");
            }
        }
    }

    fn call<'q>(out: Out<'_, 'q>, name: &str, argument: impl FnOnce(Out<'_, 'q>)) {
        out.sql(name);
        out.sql("(");
        argument(out);
        out.sql(")");
    }

    fn arith(op: Arith) -> &'static str {
        match op {
            Arith::Add => " + ",
            Arith::Sub => " - ",
            Arith::Mul => " * ",
            Arith::Div => " / ",
        }
    }

    pub(super) fn aggregate_int<'q>(tree: &'q AggInt, out: Out<'_, 'q>) {
        match tree {
            AggInt::Key => out.sql("t.g"),
            AggInt::Literal(value) => out.bind(Bind::Int(*value)),
            AggInt::Min(value) => call(out, "min", |out| write_int(value, out)),
            AggInt::Max(value) => call(out, "max", |out| write_int(value, out)),
            AggInt::Arith(op, left, right) => binary(
                out,
                |out| aggregate_int(left, out),
                arith(*op),
                |out| aggregate_int(right, out),
            ),
        }
    }

    pub(super) fn aggregate_big<'q>(tree: &'q AggBig, out: Out<'_, 'q>) {
        match tree {
            AggBig::Literal(value) => out.bind(Bind::BigInt(*value)),
            AggBig::Sum(value) => call(out, "sum", |out| write_int(value, out)),
            AggBig::Count(value) => call(out, "count", |out| write_int(value, out)),
            AggBig::CountStar => out.sql("count(*)"),
        }
    }

    pub(super) fn aggregate_bool<'q>(tree: &'q AggBool, out: Out<'_, 'q>) {
        match tree {
            AggBool::Literal(value) => out.bind(Bind::Bool(*value)),
            AggBool::Compare(op, left, right) => binary(
                out,
                |out| aggregate_int(left, out),
                comparison(*op),
                |out| aggregate_int(right, out),
            ),
            AggBool::CompareBig(op, left, right) => binary(
                out,
                |out| aggregate_big(left, out),
                comparison(*op),
                |out| aggregate_big(right, out),
            ),
            AggBool::IsNull { negated, value } => {
                out.sql("(");
                aggregate_int(value, out);
                out.sql(null_test(*negated));
            }
            AggBool::And(left, right) => binary(
                out,
                |out| aggregate_bool(left, out),
                " AND ",
                |out| aggregate_bool(right, out),
            ),
            AggBool::Or(left, right) => binary(
                out,
                |out| aggregate_bool(left, out),
                " OR ",
                |out| aggregate_bool(right, out),
            ),
            AggBool::Not(inner) => {
                out.sql("(NOT ");
                aggregate_bool(inner, out);
                out.sql(")");
            }
        }
    }

    fn comparison(op: Comparison) -> &'static str {
        match op {
            Comparison::Eq => " = ",
            Comparison::NotEq => " != ",
            Comparison::Lt => " < ",
            Comparison::LtEq => " <= ",
            Comparison::Gt => " > ",
            Comparison::GtEq => " >= ",
        }
    }

    fn null_test(negated: bool) -> &'static str {
        if negated {
            " IS NOT NULL)"
        } else {
            " IS NULL)"
        }
    }
}
