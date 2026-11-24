//! PostgreSQL table-valued functions and their result relations.
//!
//! ```rust
//! use diesel::pg::table_functions::generate_series;
//! use diesel::prelude::*;
//!
//! diesel::view! {
//!     series {
//!         value -> Integer,
//!     }
//! }
//!
//! let query = generate_series::<series::view, _, _, _>(1, 3).select(series::value);
//! assert_eq!(
//!     diesel::debug_query::<diesel::pg::Pg, _>(&query).to_string(),
//!     "SELECT \"series\".\"value\" FROM generate_series($1, $2) AS \"series\"(\"value\") -- binds: [1, 3]",
//! );
//! ```

use crate::pg::expression::expression_methods::{
    ArrayOrNullableArray, JsonOrNullableJson, JsonbOrNullableJsonb,
};
use crate::query_source::SingleColumnRelation;
use crate::sql_types::*;

crate::view! {
    /// Result columns of [`json_each`](super::json_each()).
    json_each {
        /// Object key.
        key -> Text,
        /// Object value.
        value -> Json,
    }
}
crate::view! {
    /// Result columns of [`jsonb_each`](super::jsonb_each()).
    jsonb_each {
        /// Object key.
        key -> Text,
        /// Object value.
        value -> Jsonb,
    }
}
crate::view! {
    /// Result columns of [`json_each_text`](super::json_each_text()).
    json_each_text {
        /// Object key.
        key -> Text,
        /// Textual value, or `NULL` for a `JSON` `null`.
        value -> Nullable<Text>,
    }
}
crate::view! {
    /// Result columns of [`jsonb_each_text`](super::jsonb_each_text()).
    jsonb_each_text {
        /// Object key.
        key -> Text,
        /// Textual value, or `NULL` for a `JSON` `null`.
        value -> Nullable<Text>,
    }
}
crate::view! {
    /// Result columns of [`json_array_elements`](super::json_array_elements()).
    json_array_elements {
        /// Array element.
        value -> Json,
    }
}
crate::view! {
    /// Result columns of [`jsonb_array_elements`](super::jsonb_array_elements()).
    jsonb_array_elements {
        /// Array element.
        value -> Jsonb,
    }
}
crate::view! {
    /// Result columns of [`json_array_elements_text`](super::json_array_elements_text()).
    json_array_elements_text {
        /// Textual element, or `NULL` for a `JSON` `null`.
        value -> Nullable<Text>,
    }
}
crate::view! {
    /// Result columns of [`jsonb_array_elements_text`](super::jsonb_array_elements_text()).
    jsonb_array_elements_text {
        /// Textual element, or `NULL` for a `JSON` `null`.
        value -> Nullable<Text>,
    }
}
crate::view! {
    /// Result columns of [`json_object_keys`](super::json_object_keys()).
    json_object_keys {
        /// Object key.
        value -> Text,
    }
}
crate::view! {
    /// Result columns of [`jsonb_object_keys`](super::jsonb_object_keys()).
    jsonb_object_keys {
        /// Object key.
        value -> Text,
    }
}
crate::view! {
    /// Result columns of [`jsonb_path_query`](super::jsonb_path_query()).
    jsonb_path_query {
        /// Value matching the path.
        value -> Jsonb,
    }
}
crate::view! {
    /// Result columns of [`regexp_matches`](super::regexp_matches()).
    regexp_matches {
        /// Captures, with `NULL` for unmatched groups.
        value -> Array<Nullable<Text>>,
    }
}
crate::view! {
    /// Result columns of [`regexp_split_to_table`](super::regexp_split_to_table()).
    regexp_split_to_table {
        /// Text between matches.
        value -> Text,
    }
}
crate::view! {
    /// Result columns of [`string_to_table`](super::string_to_table()).
    string_to_table {
        /// Field, or `NULL` when it matches the null marker.
        value -> Nullable<Text>,
    }
}
crate::view! {
    /// Result columns of [`generate_subscripts`](super::generate_subscripts()).
    generate_subscripts {
        /// Array subscript.
        value -> Integer,
    }
}
crate::view! {
    /// Result columns of [`pg_get_keywords`](super::pg_get_keywords()).
    pg_get_keywords {
        /// Keyword.
        word -> Text,
        /// Parser category code.
        catcode -> CChar,
        /// Whether the keyword can be a bare column label.
        barelabel -> Bool,
        /// Parser category description.
        catdesc -> Text,
        /// Column label category description.
        baredesc -> Text,
    }
}

crate::allow_tables_to_appear_in_same_query!(
    json_each,
    jsonb_each,
    json_each_text,
    jsonb_each_text,
    json_array_elements,
    jsonb_array_elements,
    json_array_elements_text,
    jsonb_array_elements_text,
    json_object_keys,
    jsonb_object_keys,
    jsonb_path_query,
    regexp_matches,
    regexp_split_to_table,
    string_to_table,
    generate_subscripts,
    pg_get_keywords,
);

/// SQL types accepted by numeric `generate_series` overloads.
pub trait SeriesNumber: SingleValue + private::Sealed {}
impl SeriesNumber for Integer {}
impl SeriesNumber for BigInt {}
impl SeriesNumber for Numeric {}

/// SQL types accepted by interval-stepped `generate_series` overloads.
pub trait SeriesTimestamp: SingleValue + private::Sealed {}
impl SeriesTimestamp for Timestamp {}
impl SeriesTimestamp for Timestamptz {}

mod private {
    pub trait Sealed {}
    impl Sealed for crate::sql_types::Integer {}
    impl Sealed for crate::sql_types::BigInt {}
    impl Sealed for crate::sql_types::Numeric {}
    impl Sealed for crate::sql_types::Timestamp {}
    impl Sealed for crate::sql_types::Timestamptz {}
}

#[crate::declare_sql_function(generate_return_type_helpers = true)]
#[backends(crate::pg::Pg)]
extern "SQL" {
    /// Expands a `JSON` object into key/value rows.
    #[query_source(json_each)]
    fn json_each<Document: JsonOrNullableJson + SingleValue>(
        document: Document,
    ) -> json_each::SqlType;
    /// Expands a `JSONB` object into key/value rows.
    #[query_source(jsonb_each)]
    fn jsonb_each<Document: JsonbOrNullableJsonb + SingleValue>(
        document: Document,
    ) -> jsonb_each::SqlType;
    /// Expands a `JSON` object into textual key/value rows.
    #[query_source(json_each_text)]
    fn json_each_text<Document: JsonOrNullableJson + SingleValue>(
        document: Document,
    ) -> json_each_text::SqlType;
    /// Expands a `JSONB` object into textual key/value rows.
    #[query_source(jsonb_each_text)]
    fn jsonb_each_text<Document: JsonbOrNullableJsonb + SingleValue>(
        document: Document,
    ) -> jsonb_each_text::SqlType;
    /// Expands a `JSON` array into rows.
    #[query_source(json_array_elements, base_type)]
    fn json_array_elements<Document: JsonOrNullableJson + SingleValue>(
        document: Document,
    ) -> json_array_elements::SqlType;
    /// Expands a `JSONB` array into rows.
    #[query_source(jsonb_array_elements, base_type)]
    fn jsonb_array_elements<Document: JsonbOrNullableJsonb + SingleValue>(
        document: Document,
    ) -> jsonb_array_elements::SqlType;
    /// Expands a `JSON` array into nullable text rows.
    #[query_source(json_array_elements_text, base_type)]
    fn json_array_elements_text<Document: JsonOrNullableJson + SingleValue>(
        document: Document,
    ) -> json_array_elements_text::SqlType;
    /// Expands a `JSONB` array into nullable text rows.
    #[query_source(jsonb_array_elements_text, base_type)]
    fn jsonb_array_elements_text<Document: JsonbOrNullableJsonb + SingleValue>(
        document: Document,
    ) -> jsonb_array_elements_text::SqlType;
    /// Returns the keys of a `JSON` object.
    #[query_source(json_object_keys, base_type)]
    fn json_object_keys<Document: JsonOrNullableJson + SingleValue>(
        document: Document,
    ) -> json_object_keys::SqlType;
    /// Returns the keys of a `JSONB` object.
    #[query_source(jsonb_object_keys, base_type)]
    fn jsonb_object_keys<Document: JsonbOrNullableJsonb + SingleValue>(
        document: Document,
    ) -> jsonb_object_keys::SqlType;
    /// Returns the `JSONB` values matching a `Jsonpath` expression.
    #[query_source(jsonb_path_query, base_type)]
    fn jsonb_path_query<Document: JsonbOrNullableJsonb + SingleValue>(
        document: Document,
        path: Jsonpath,
    ) -> jsonb_path_query::SqlType;
    /// Evaluates a `Jsonpath` expression with named variables.
    #[sql_name = "jsonb_path_query"]
    #[query_source(jsonb_path_query, base_type)]
    fn jsonb_path_query_with_vars<
        Document: JsonbOrNullableJsonb + SingleValue,
        Variables: JsonbOrNullableJsonb + SingleValue,
    >(
        document: Document,
        path: Jsonpath,
        variables: Variables,
    ) -> jsonb_path_query::SqlType;
    /// Evaluates a `Jsonpath` expression with optional error suppression.
    #[sql_name = "jsonb_path_query"]
    #[query_source(jsonb_path_query, base_type)]
    fn jsonb_path_query_with_silent<
        Document: JsonbOrNullableJsonb + SingleValue,
        Variables: JsonbOrNullableJsonb + SingleValue,
    >(
        document: Document,
        path: Jsonpath,
        variables: Variables,
        silent: Bool,
    ) -> jsonb_path_query::SqlType;
    /// Returns regular-expression capture arrays, including unmatched nullable captures.
    #[query_source(regexp_matches, base_type)]
    fn regexp_matches(string: Text, pattern: Text) -> regexp_matches::SqlType;
    /// Returns regular-expression captures using the supplied flags.
    #[sql_name = "regexp_matches"]
    #[query_source(regexp_matches, base_type)]
    fn regexp_matches_with_flags(
        string: Text,
        pattern: Text,
        flags: Text,
    ) -> regexp_matches::SqlType;
    /// Splits text at matches of a regular expression.
    #[query_source(regexp_split_to_table, base_type)]
    fn regexp_split_to_table(string: Text, pattern: Text) -> regexp_split_to_table::SqlType;
    /// Splits text at regular-expression matches using the supplied flags.
    #[sql_name = "regexp_split_to_table"]
    #[query_source(regexp_split_to_table, base_type)]
    fn regexp_split_to_table_with_flags(
        string: Text,
        pattern: Text,
        flags: Text,
    ) -> regexp_split_to_table::SqlType;
    /// Splits text into rows at a delimiter.
    #[query_source(string_to_table, base_type)]
    fn string_to_table(string: Text, delimiter: Text) -> string_to_table::SqlType;
    /// Splits text into rows and replaces the null marker with `NULL`.
    #[sql_name = "string_to_table"]
    #[query_source(string_to_table, base_type)]
    fn string_to_table_with_null_string(
        string: Text,
        delimiter: Text,
        null_string: Text,
    ) -> string_to_table::SqlType;
    /// Returns the valid subscripts of an array dimension.
    #[query_source(generate_subscripts, base_type)]
    fn generate_subscripts<ArrayValue: ArrayOrNullableArray + SingleValue>(
        array: ArrayValue,
        dimension: Integer,
    ) -> generate_subscripts::SqlType;
    /// Returns array subscripts in optionally reversed order.
    #[sql_name = "generate_subscripts"]
    #[query_source(generate_subscripts, base_type)]
    fn generate_subscripts_with_reverse<ArrayValue: ArrayOrNullableArray + SingleValue>(
        array: ArrayValue,
        dimension: Integer,
        reverse: Bool,
    ) -> generate_subscripts::SqlType;
    /// Lists PostgreSQL keywords and their parser categories.
    #[query_source(pg_get_keywords)]
    fn pg_get_keywords() -> pg_get_keywords::SqlType;
    /// Generates numeric rows using a caller-declared one-column relation.
    #[query_source(Relation, base_type)]
    fn generate_series<Relation: SingleColumnRelation<ColumnSqlType = Value>, Value: SeriesNumber>(
        start: Value,
        stop: Value,
    ) -> Relation::SqlType;
    /// Generates numeric rows with an explicit step.
    #[sql_name = "generate_series"]
    #[query_source(Relation, base_type)]
    fn generate_series_with_step<
        Relation: SingleColumnRelation<ColumnSqlType = Value>,
        Value: SeriesNumber,
    >(
        start: Value,
        stop: Value,
        step: Value,
    ) -> Relation::SqlType;
    /// Generates timestamp rows with an interval step.
    #[sql_name = "generate_series"]
    #[query_source(Relation, base_type)]
    fn generate_series_with_interval<
        Relation: SingleColumnRelation<ColumnSqlType = Value>,
        Value: SeriesTimestamp,
    >(
        start: Value,
        stop: Value,
        step: Interval,
    ) -> Relation::SqlType;
    /// Generates timezone-aware timestamp rows in a named timezone on PostgreSQL 16 or later.
    #[sql_name = "generate_series"]
    #[query_source(Relation, base_type)]
    fn generate_series_with_timezone<Relation: SingleColumnRelation<ColumnSqlType = Timestamptz>>(
        start: Timestamptz,
        stop: Timestamptz,
        step: Interval,
        timezone: Text,
    ) -> Relation::SqlType;
    /// Expands an array into a caller-declared one-column relation matching its element type.
    #[query_source(Relation, base_type)]
    fn unnest<
        Relation: SingleColumnRelation<ColumnSqlType = ArrayValue::Inner>,
        ArrayValue: ArrayOrNullableArray + SingleValue,
    >(
        array: ArrayValue,
    ) -> Relation::SqlType;
}

/// Return types of PostgreSQL table-valued functions.
pub mod helper_types {
    #[doc(inline)]
    pub use super::return_type_helpers::*;
}
