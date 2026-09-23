//! Random expression trees built through diesel's query builder, for checking the sql it renders
//! against postgres' own parser and sqlite's own evaluation.
//!
//! One sql type per operator family is enough, since `Cidr`, `Json`, multiranges and the other
//! siblings render through the same operator code as `Inet`, `Jsonb` and `Int4range`.

mod tree;

pub use tree::*;

diesel::table! {
    t (id) {
        id -> Integer,
        a -> Integer,
        b -> Nullable<Integer>,
        s -> Text,
        n -> Nullable<Text>,
        f -> Bool,
        g -> Nullable<Integer>,
        j -> Nullable<Json>,
        jb -> Nullable<Jsonb>,
        ia -> Nullable<Array<Integer>>,
        r -> Nullable<Int4range>,
        ip -> Nullable<Inet>,
        ts -> Nullable<Timestamp>,
        tz -> Nullable<Timestamptz>,
        bin -> Nullable<Binary>,
    }
}

/// Maps a tree onto boxed diesel expressions for one backend. The including module supplies
/// the nodes whose dsl differs between backends, `distinct`, `matches`, `json_field` and
/// `nulls_order`, and builds the postgres-only nodes in `postgres_int`, `postgres_text`,
/// `postgres_json` and `postgres_bool`.
macro_rules! builder {
    ($db:ty) => {
        use super::{
            AggBig, AggBool, AggInt, Arith, Bool, Comparison, Grouping, Int, IntColumn, Json,
            JsonKey, Order, Query, Subquery, Text, TextColumn, t,
        };
        use diesel::dsl::{case_when, count, count_star, exists, max, min, not, sum};
        use diesel::expression::{
            AppearsOnTable, BoxableExpression, Expression, SelectableExpression, ValidGrouping,
            is_aggregate,
        };
        use diesel::prelude::*;
        use diesel::query_builder::{AstPass, QueryFragment, QueryId};
        use diesel::sql_types::{
            BigInt, Bool as SqlBool, Integer, Json as SqlJson, Nullable, Text as SqlText,
        };

        pub type Boxed<'a, ST> =
            Box<dyn BoxableExpression<t::table, $db, SqlType = Nullable<ST>> + 'a>;

        pub type Statement<'a> =
            t::BoxedQuery<'a, $db, (Nullable<Integer>, Nullable<SqlText>, Nullable<SqlBool>)>;

        pub type Subselect<'a> = t::BoxedQuery<'a, $db, Nullable<Integer>>;

        /// An expression of a query grouped by `t.g`, which may aggregate.
        pub type Aggregate<'a, ST> = Box<
            dyn BoxableExpression<t::table, $db, t::g, is_aggregate::Yes, SqlType = Nullable<ST>>
                + 'a,
        >;

        pub type GroupStatement<'a> = diesel::dsl::IntoBoxed<
            'a,
            diesel::dsl::Select<
                diesel::dsl::GroupBy<t::table, t::g>,
                (t::g, Aggregate<'a, Integer>, Aggregate<'a, BigInt>),
            >,
            $db,
        >;

        /// A boxed aggregate integer, which unlike the box itself takes `+`, `-`, `*` and `/`.
        #[derive(diesel::sql_types::DieselNumericOps)]
        pub struct AggNumber<'a>(Aggregate<'a, Integer>);

        impl Expression for AggNumber<'_> {
            type SqlType = Nullable<Integer>;
        }

        impl QueryFragment<$db> for AggNumber<'_> {
            fn walk_ast<'b>(&'b self, pass: AstPass<'_, 'b, $db>) -> QueryResult<()> {
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

        impl QueryFragment<$db> for Number<'_> {
            fn walk_ast<'b>(&'b self, pass: AstPass<'_, 'b, $db>) -> QueryResult<()> {
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
                    nulls: None,
                }) => statement.then_order_by(int(key).asc()),
                Some(Order {
                    key,
                    descending: true,
                    nulls: None,
                }) => statement.then_order_by(int(key).desc()),
                Some(Order {
                    key,
                    descending,
                    nulls: Some(nulls),
                }) => nulls_order(statement, int(key), *descending, *nulls),
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
                AggBool::And(left, right) => {
                    Box::new(aggregate_bool(left).and(aggregate_bool(right)))
                }
                AggBool::Or(left, right) => {
                    Box::new(aggregate_bool(left).or(aggregate_bool(right)))
                }
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
                        (Some((when, then)), None) => {
                            Box::new(first.when(boolean(when), int(then)))
                        }
                        (Some((when, then)), Some(otherwise)) => Box::new(
                            first
                                .when(boolean(when), int(then))
                                .otherwise(int(otherwise)),
                        ),
                    }
                }
                Int::FromText(value) => Box::new(text(value).fallible_cast::<Nullable<Integer>>()),
                Int::Scalar(subquery) => Box::new(subselect(subquery).single_value()),
                Int::Postgres(tree) => postgres_int(tree),
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
                Text::Postgres(tree) => postgres_text(tree),
            }
        }

        pub fn json(tree: &Json) -> Boxed<'_, SqlJson> {
            match tree {
                Json::Column => Box::new(t::j),
                Json::Literal(value) => Box::new(value.into_sql::<Nullable<SqlJson>>()),
                Json::Field(value, key) => json_field(json(value), key),
                Json::FromText(value) => Box::new(text(value).fallible_cast::<Nullable<SqlJson>>()),
                Json::Postgres(tree) => postgres_json(tree),
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
                    negated,
                    left,
                    right,
                } => distinct(*negated, int(left), int(right)),
                Bool::Match {
                    matcher,
                    negated,
                    value,
                    pattern,
                    escape,
                } => matches(*matcher, *negated, text(value), text(pattern), *escape),
                Bool::And(left, right) => Box::new(boolean(left).and(boolean(right))),
                Bool::Or(left, right) => Box::new(boolean(left).or(boolean(right))),
                Bool::Not(inner) => Box::new(not(boolean(inner))),
                Bool::Postgres(tree) => postgres_bool(tree),
            }
        }
    };
}

pub mod pg;
pub mod sqlite;
