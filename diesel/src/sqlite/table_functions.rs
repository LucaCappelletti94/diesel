//! SQLite's built-in table-valued functions.
//!
//! Pragma functions require builds without `SQLITE_OMIT_PRAGMA` or `SQLITE_OMIT_VIRTUALTABLE`, in addition to each function's requirements.
//! An unavailable function fails when SQLite prepares the query.
//!
//! `JSON` functions accept a caller-defined, schema-free `view!` containing any subset of `key`, `value`, `type`, `atom`, `id`, `parent`, `fullkey`, and `path`.
//! `key` is an integer array index, a text object key, or `NULL` at a root, while `id` is an integer and `parent` is a nullable integer (`NULL` throughout `json_each`).
//! `type`, `fullkey`, and `path` are text, and `value` holds integers for integers and booleans, reals for real numbers, text for strings, and `NULL` for nulls.
//! Containers in `value` are text for `json_each` and `json_tree`, or binary for `jsonb_each` and `jsonb_tree`, while `atom` holds the primitive value or `NULL` for containers.
//! Choose column SQL types for the document being queried, since comparisons preserve these storage classes and unknown column names fail at prepare.

use crate::query_source::TableFunctionRelation;
use crate::sql_types::{Nullable, SingleValue, Text};
use crate::sqlite::expression::expression_methods::TextOrNullableTextOrBinaryOrNullableBinary;

crate::view! {
    /// Table columns on SQLite 3.16.0+, without `SQLITE_OMIT_SCHEMA_PRAGMAS`.
    pragma_table_info {
        /// Column rank.
        cid -> Integer,
        /// Column name.
        name -> Text,
        /// Declared type name.
        #[sql_name = "type"]
        type_name -> Text,
        /// Whether the column disallows nulls.
        notnull -> Bool,
        /// Default expression, if declared.
        dflt_value -> Nullable<Text>,
        /// One-based primary-key position, or zero.
        pk -> Integer,
    }
}

crate::view! {
    /// All table columns on SQLite 3.26.0+, without `SQLITE_OMIT_SCHEMA_PRAGMAS`.
    pragma_table_xinfo {
        /// Column rank.
        cid -> Integer,
        /// Column name.
        name -> Text,
        /// Declared type name.
        #[sql_name = "type"]
        type_name -> Text,
        /// Whether the column disallows nulls.
        notnull -> Bool,
        /// Default expression, if declared.
        dflt_value -> Nullable<Text>,
        /// One-based primary-key position, or zero.
        pk -> Integer,
        /// Hidden-column or generated-column classification.
        hidden -> Integer,
    }
}

crate::view! {
    /// Tables and views on SQLite 3.37.0+, without `SQLITE_OMIT_SCHEMA_PRAGMAS`.
    pragma_table_list {
        /// Containing database name.
        schema -> Text,
        /// Table or view name.
        name -> Text,
        /// Table, view, virtual-table, or shadow-table classification.
        #[sql_name = "type"]
        type_name -> Text,
        /// Column count including hidden and generated columns.
        ncol -> Integer,
        /// Whether the table uses `WITHOUT ROWID`.
        wr -> Bool,
        /// Whether the table uses `STRICT`.
        strict -> Bool,
    }
}

crate::view! {
    /// Table indexes on SQLite 3.16.0+, without `SQLITE_OMIT_SCHEMA_PRAGMAS`.
    pragma_index_list {
        /// Index sequence number.
        seq -> Integer,
        /// Index name.
        name -> Text,
        /// Whether the index enforces uniqueness.
        unique -> Bool,
        /// Explicit, unique-constraint, or primary-key origin.
        origin -> Text,
        /// Whether the index is partial.
        partial -> Bool,
    }
}

crate::view! {
    /// Indexed columns on SQLite 3.16.0+, without `SQLITE_OMIT_SCHEMA_PRAGMAS`.
    pragma_index_info {
        /// Position within the index.
        seqno -> Integer,
        /// Table column rank, or a negative row identifier or expression marker.
        cid -> Integer,
        /// Column name, absent for row identifiers and expressions.
        name -> Nullable<Text>,
    }
}

crate::view! {
    /// Indexed and auxiliary columns on SQLite 3.16.0+, without `SQLITE_OMIT_SCHEMA_PRAGMAS`.
    pragma_index_xinfo {
        /// Position within the index.
        seqno -> Integer,
        /// Table column rank, or a negative row identifier or expression marker.
        cid -> Integer,
        /// Column name, absent for row identifiers and expressions.
        name -> Nullable<Text>,
        /// Whether this column sorts descending.
        desc -> Bool,
        /// Collation name, if applicable.
        coll -> Nullable<Text>,
        /// Whether this column belongs to the index key.
        key -> Bool,
    }
}

crate::view! {
    /// Foreign keys on SQLite 3.16.0+, without `SQLITE_OMIT_FOREIGN_KEY`.
    pragma_foreign_key_list {
        /// Foreign-key identifier.
        id -> Integer,
        /// Position within the foreign key.
        seq -> Integer,
        /// Referenced table name.
        #[sql_name = "table"]
        table_name -> Text,
        /// Referencing column name.
        #[sql_name = "from"]
        from_column -> Text,
        /// Referenced column name, absent for an implicit primary key.
        #[sql_name = "to"]
        to_column -> Nullable<Text>,
        /// Update action.
        on_update -> Text,
        /// Delete action.
        on_delete -> Text,
        /// Matching rule.
        #[sql_name = "match"]
        match_rule -> Text,
    }
}

crate::view! {
    /// Foreign-key violations on SQLite 3.20.0+, without `SQLITE_OMIT_FOREIGN_KEY` or `SQLITE_OMIT_TRIGGER`.
    pragma_foreign_key_check {
        /// Referencing table name.
        #[sql_name = "table"]
        table_name -> Text,
        /// Violating row identifier, absent for `WITHOUT ROWID` tables.
        rowid -> Nullable<BigInt>,
        /// Referenced table name.
        parent -> Text,
        /// Foreign-key identifier.
        fkid -> Integer,
    }
}

crate::view! {
    /// Attached databases on SQLite 3.16.0+, without `SQLITE_OMIT_SCHEMA_PRAGMAS`.
    pragma_database_list {
        /// Database sequence number.
        seq -> Integer,
        /// Database name.
        name -> Text,
        /// Database filename, empty for in-memory databases.
        file -> Text,
    }
}

crate::view! {
    /// Collations on SQLite 3.16.0+, without `SQLITE_OMIT_SCHEMA_PRAGMAS`.
    pragma_collation_list {
        /// Collation sequence number.
        seq -> Integer,
        /// Collation name.
        name -> Text,
    }
}

crate::view! {
    /// Function signatures on SQLite 3.31.0+, without `SQLITE_OMIT_SCHEMA_PRAGMAS` or `SQLITE_OMIT_INTROSPECTION_PRAGMAS`.
    pragma_function_list {
        /// Function name.
        name -> Text,
        /// Whether the function is built in.
        builtin -> Bool,
        /// Scalar, aggregate, or window-function classification.
        #[sql_name = "type"]
        type_name -> Text,
        /// Preferred text encoding.
        enc -> Text,
        /// Argument count, or minus one for variadic functions.
        narg -> Integer,
        /// Function property flags.
        flags -> Integer,
    }
}

crate::view! {
    /// Virtual-table modules on SQLite 3.20.0+, requiring `SQLITE_INTROSPECTION_PRAGMAS` before 3.30.0 and builds without `SQLITE_OMIT_SCHEMA_PRAGMAS` or `SQLITE_OMIT_INTROSPECTION_PRAGMAS`.
    pragma_module_list {
        /// Module name.
        name -> Text,
    }
}

crate::view! {
    /// Pragmas on SQLite 3.20.0+, requiring `SQLITE_INTROSPECTION_PRAGMAS` before 3.30.0 and builds without `SQLITE_OMIT_INTROSPECTION_PRAGMAS`.
    pragma_pragma_list {
        /// Pragma name.
        name -> Text,
    }
}

crate::view! {
    /// Compile options on SQLite 3.16.0+, without `SQLITE_OMIT_COMPILEOPTION_DIAGS`.
    pragma_compile_options {
        /// Enabled compile option.
        compile_options -> Text,
    }
}

crate::view! {
    /// Integrity results on SQLite 3.20.0+, without `SQLITE_OMIT_INTEGRITY_CHECK`.
    pragma_integrity_check {
        /// Integrity error, or `ok`.
        integrity_check -> Text,
    }
}

crate::view! {
    /// Quick integrity results on SQLite 3.20.0+, without `SQLITE_OMIT_INTEGRITY_CHECK`.
    pragma_quick_check {
        /// Integrity error, or `ok`.
        quick_check -> Text,
    }
}

crate::allow_tables_to_appear_in_same_query!(
    pragma_table_info,
    pragma_table_xinfo,
    pragma_table_list,
    pragma_index_list,
    pragma_index_info,
    pragma_index_xinfo,
    pragma_foreign_key_list,
    pragma_foreign_key_check,
    pragma_database_list,
    pragma_collation_list,
    pragma_function_list,
    pragma_module_list,
    pragma_pragma_list,
    pragma_compile_options,
    pragma_integrity_check,
    pragma_quick_check,
);

#[crate::declare_sql_function(generate_return_type_helpers = true)]
#[backends(crate::sqlite::Sqlite)]
extern "SQL" {
    /// Lists table columns on SQLite 3.16.0+, without `SQLITE_OMIT_SCHEMA_PRAGMAS`.
    #[query_source(pragma_table_info)]
    fn pragma_table_info(table_name: Text) -> pragma_table_info::SqlType;

    /// Lists table columns in a schema on SQLite 3.16.0+, without `SQLITE_OMIT_SCHEMA_PRAGMAS`.
    #[sql_name = "pragma_table_info"]
    #[query_source(pragma_table_info)]
    fn pragma_table_info_with_schema(table_name: Text, schema: Text) -> pragma_table_info::SqlType;

    /// Includes hidden and generated columns on SQLite 3.26.0+, without `SQLITE_OMIT_SCHEMA_PRAGMAS`.
    #[query_source(pragma_table_xinfo)]
    fn pragma_table_xinfo(table_name: Text) -> pragma_table_xinfo::SqlType;

    /// Includes hidden and generated columns in a schema on SQLite 3.26.0+, without `SQLITE_OMIT_SCHEMA_PRAGMAS`.
    #[sql_name = "pragma_table_xinfo"]
    #[query_source(pragma_table_xinfo)]
    fn pragma_table_xinfo_with_schema(
        table_name: Text,
        schema: Text,
    ) -> pragma_table_xinfo::SqlType;

    /// Lists tables and views on SQLite 3.37.0+, without `SQLITE_OMIT_SCHEMA_PRAGMAS`.
    #[query_source(pragma_table_list)]
    fn pragma_table_list() -> pragma_table_list::SqlType;

    /// Lists tables matching a name on SQLite 3.37.0+, without `SQLITE_OMIT_SCHEMA_PRAGMAS`.
    #[sql_name = "pragma_table_list"]
    #[query_source(pragma_table_list)]
    fn pragma_table_list_for_table(table_name: Text) -> pragma_table_list::SqlType;

    /// Lists table indexes on SQLite 3.16.0+, without `SQLITE_OMIT_SCHEMA_PRAGMAS`.
    #[query_source(pragma_index_list)]
    fn pragma_index_list(table_name: Text) -> pragma_index_list::SqlType;

    /// Lists table indexes in a schema on SQLite 3.16.0+, without `SQLITE_OMIT_SCHEMA_PRAGMAS`.
    #[sql_name = "pragma_index_list"]
    #[query_source(pragma_index_list)]
    fn pragma_index_list_with_schema(table_name: Text, schema: Text) -> pragma_index_list::SqlType;

    /// Lists indexed columns on SQLite 3.16.0+, without `SQLITE_OMIT_SCHEMA_PRAGMAS`.
    #[query_source(pragma_index_info)]
    fn pragma_index_info(index_name: Text) -> pragma_index_info::SqlType;

    /// Lists indexed columns in a schema on SQLite 3.16.0+, without `SQLITE_OMIT_SCHEMA_PRAGMAS`.
    #[sql_name = "pragma_index_info"]
    #[query_source(pragma_index_info)]
    fn pragma_index_info_with_schema(index_name: Text, schema: Text) -> pragma_index_info::SqlType;

    /// Includes auxiliary index columns on SQLite 3.16.0+, without `SQLITE_OMIT_SCHEMA_PRAGMAS`.
    #[query_source(pragma_index_xinfo)]
    fn pragma_index_xinfo(index_name: Text) -> pragma_index_xinfo::SqlType;

    /// Includes auxiliary index columns in a schema on SQLite 3.16.0+, without `SQLITE_OMIT_SCHEMA_PRAGMAS`.
    #[sql_name = "pragma_index_xinfo"]
    #[query_source(pragma_index_xinfo)]
    fn pragma_index_xinfo_with_schema(
        index_name: Text,
        schema: Text,
    ) -> pragma_index_xinfo::SqlType;

    /// Lists foreign keys on SQLite 3.16.0+, without `SQLITE_OMIT_FOREIGN_KEY`.
    #[query_source(pragma_foreign_key_list)]
    fn pragma_foreign_key_list(table_name: Text) -> pragma_foreign_key_list::SqlType;

    /// Lists foreign keys in a schema on SQLite 3.16.0+, without `SQLITE_OMIT_FOREIGN_KEY`.
    #[sql_name = "pragma_foreign_key_list"]
    #[query_source(pragma_foreign_key_list)]
    fn pragma_foreign_key_list_with_schema(
        table_name: Text,
        schema: Text,
    ) -> pragma_foreign_key_list::SqlType;

    /// Lists foreign-key violations on SQLite 3.20.0+, without `SQLITE_OMIT_FOREIGN_KEY` or `SQLITE_OMIT_TRIGGER`.
    #[query_source(pragma_foreign_key_check)]
    fn pragma_foreign_key_check() -> pragma_foreign_key_check::SqlType;

    /// Checks table foreign keys on SQLite 3.33.0+, without `SQLITE_OMIT_FOREIGN_KEY` or `SQLITE_OMIT_TRIGGER`.
    #[sql_name = "pragma_foreign_key_check"]
    #[query_source(pragma_foreign_key_check)]
    fn pragma_foreign_key_check_for_table(table_name: Text) -> pragma_foreign_key_check::SqlType;

    /// Checks foreign keys in a schema on SQLite 3.33.0+, using `NULL` for every table and requiring foreign-key and trigger support.
    #[sql_name = "pragma_foreign_key_check"]
    #[query_source(pragma_foreign_key_check)]
    fn pragma_foreign_key_check_with_schema(
        table_name: Nullable<Text>,
        schema: Text,
    ) -> pragma_foreign_key_check::SqlType;

    /// Lists databases on SQLite 3.16.0+, without `SQLITE_OMIT_SCHEMA_PRAGMAS`.
    #[query_source(pragma_database_list)]
    fn pragma_database_list() -> pragma_database_list::SqlType;

    /// Lists collations on SQLite 3.16.0+, without `SQLITE_OMIT_SCHEMA_PRAGMAS`.
    #[query_source(pragma_collation_list)]
    fn pragma_collation_list() -> pragma_collation_list::SqlType;

    /// Lists function signatures on SQLite 3.31.0+, without `SQLITE_OMIT_SCHEMA_PRAGMAS` or `SQLITE_OMIT_INTROSPECTION_PRAGMAS`.
    #[query_source(pragma_function_list)]
    fn pragma_function_list() -> pragma_function_list::SqlType;

    /// Lists modules on SQLite 3.20.0+, with the compile requirements of [`mod@pragma_module_list`].
    #[query_source(pragma_module_list)]
    fn pragma_module_list() -> pragma_module_list::SqlType;

    /// Lists pragmas on SQLite 3.20.0+, with the compile requirements of [`mod@pragma_pragma_list`].
    #[query_source(pragma_pragma_list)]
    fn pragma_pragma_list() -> pragma_pragma_list::SqlType;

    /// Lists compile options on SQLite 3.16.0+, without `SQLITE_OMIT_COMPILEOPTION_DIAGS`.
    #[query_source(pragma_compile_options)]
    fn pragma_compile_options() -> pragma_compile_options::SqlType;

    /// Checks integrity on SQLite 3.20.0+, without `SQLITE_OMIT_INTEGRITY_CHECK`.
    #[query_source(pragma_integrity_check)]
    fn pragma_integrity_check() -> pragma_integrity_check::SqlType;

    /// Checks one table on SQLite 3.33.0+, without `SQLITE_OMIT_INTEGRITY_CHECK`.
    #[sql_name = "pragma_integrity_check"]
    #[query_source(pragma_integrity_check)]
    fn pragma_integrity_check_for_table(table_name: Text) -> pragma_integrity_check::SqlType;

    /// Checks a schema on SQLite 3.37.0+, using `NULL` for every table and requiring builds without `SQLITE_OMIT_INTEGRITY_CHECK`.
    #[sql_name = "pragma_integrity_check"]
    #[query_source(pragma_integrity_check)]
    fn pragma_integrity_check_with_schema(
        table_name: Nullable<Text>,
        schema: Text,
    ) -> pragma_integrity_check::SqlType;

    /// Checks integrity without index-content or uniqueness checks on SQLite 3.20.0+, without `SQLITE_OMIT_INTEGRITY_CHECK`.
    #[query_source(pragma_quick_check)]
    fn pragma_quick_check() -> pragma_quick_check::SqlType;

    /// Quickly checks one table on SQLite 3.33.0+, without `SQLITE_OMIT_INTEGRITY_CHECK`.
    #[sql_name = "pragma_quick_check"]
    #[query_source(pragma_quick_check)]
    fn pragma_quick_check_for_table(table_name: Text) -> pragma_quick_check::SqlType;

    /// Quickly checks a schema on SQLite 3.37.0+, using `NULL` for every table and requiring builds without `SQLITE_OMIT_INTEGRITY_CHECK`.
    #[sql_name = "pragma_quick_check"]
    #[query_source(pragma_quick_check)]
    fn pragma_quick_check_with_schema(
        table_name: Nullable<Text>,
        schema: Text,
    ) -> pragma_quick_check::SqlType;

    /// Expands immediate `JSON` children on SQLite 3.9.0+, requiring `SQLITE_ENABLE_JSON1` before 3.38.0 and builds without `SQLITE_OMIT_JSON` or `SQLITE_OMIT_VIRTUALTABLE`.
    #[query_source(Relation)]
    fn json_each<
        Relation: TableFunctionRelation,
        Document: TextOrNullableTextOrBinaryOrNullableBinary + SingleValue,
    >(
        document: Document,
    ) -> Relation::SqlType;

    /// Expands immediate `JSON` children at a path on SQLite 3.9.0+, with the compile requirements of [`json_each()`].
    #[sql_name = "json_each"]
    #[query_source(Relation)]
    fn json_each_with_path<
        Relation: TableFunctionRelation,
        Document: TextOrNullableTextOrBinaryOrNullableBinary + SingleValue,
    >(
        document: Document,
        path: Text,
    ) -> Relation::SqlType;

    /// Recursively expands `JSON` on SQLite 3.9.0+, with the compile requirements of [`json_each()`].
    #[query_source(Relation)]
    fn json_tree<
        Relation: TableFunctionRelation,
        Document: TextOrNullableTextOrBinaryOrNullableBinary + SingleValue,
    >(
        document: Document,
    ) -> Relation::SqlType;

    /// Recursively expands `JSON` at a path on SQLite 3.9.0+, with the compile requirements of [`json_each()`].
    #[sql_name = "json_tree"]
    #[query_source(Relation)]
    fn json_tree_with_path<
        Relation: TableFunctionRelation,
        Document: TextOrNullableTextOrBinaryOrNullableBinary + SingleValue,
    >(
        document: Document,
        path: Text,
    ) -> Relation::SqlType;

    /// Expands immediate `JSON` children with binary containers on SQLite 3.51.0+, without `SQLITE_OMIT_JSON` or `SQLITE_OMIT_VIRTUALTABLE`.
    #[query_source(Relation)]
    fn jsonb_each<
        Relation: TableFunctionRelation,
        Document: TextOrNullableTextOrBinaryOrNullableBinary + SingleValue,
    >(
        document: Document,
    ) -> Relation::SqlType;

    /// Expands immediate `JSON` children at a path with binary containers on SQLite 3.51.0+, with the compile requirements of [`jsonb_each()`].
    #[sql_name = "jsonb_each"]
    #[query_source(Relation)]
    fn jsonb_each_with_path<
        Relation: TableFunctionRelation,
        Document: TextOrNullableTextOrBinaryOrNullableBinary + SingleValue,
    >(
        document: Document,
        path: Text,
    ) -> Relation::SqlType;

    /// Recursively expands `JSON` with binary containers on SQLite 3.51.0+, with the compile requirements of [`jsonb_each()`].
    #[query_source(Relation)]
    fn jsonb_tree<
        Relation: TableFunctionRelation,
        Document: TextOrNullableTextOrBinaryOrNullableBinary + SingleValue,
    >(
        document: Document,
    ) -> Relation::SqlType;

    /// Recursively expands `JSON` at a path with binary containers on SQLite 3.51.0+, with the compile requirements of [`jsonb_each()`].
    #[sql_name = "jsonb_tree"]
    #[query_source(Relation)]
    fn jsonb_tree_with_path<
        Relation: TableFunctionRelation,
        Document: TextOrNullableTextOrBinaryOrNullableBinary + SingleValue,
    >(
        document: Document,
        path: Text,
    ) -> Relation::SqlType;
}

/// Return types of SQLite table-valued functions.
pub mod helper_types {
    #[doc(inline)]
    pub use super::return_type_helpers::*;
}
