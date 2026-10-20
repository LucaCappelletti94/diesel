//! Typed SQLite table-column metadata.

use crate::deserialize::{Queryable, Result};
use crate::query_builder::{AstPass, Query, QueryFragment, QueryId};
use crate::query_dsl::RunQueryDslSupport;
use crate::result::QueryResult;
use crate::sql_types::{Bool, Integer, Nullable, Text};
use crate::sqlite::Sqlite;
use alloc::string::String;
use core::num::NonZeroU32;

use super::{PerSchema, Pragma, PragmaLiteral, PragmaQuery};

/// SQL types of `(cid, name, type, notnull, dflt_value, pk)`, where `pk` is the primary-key ordinal or zero.
pub type TableInfoSqlType = (Integer, Text, Text, Bool, Nullable<Text>, Integer);

/// SQL types of `(cid, name, type, notnull, dflt_value, pk, hidden)`, where `pk` is the primary-key ordinal or zero and `hidden` classifies the column kind.
pub type TableXInfoSqlType = (Integer, Text, Text, Bool, Nullable<Text>, Integer, Integer);

#[derive(Debug)]
struct TableInfoPragma;

impl Pragma for TableInfoPragma {
    const NAME: &'static str = "table_info";
    type Scope = PerSchema;
}

#[derive(Debug)]
struct TableXInfoPragma;

impl Pragma for TableXInfoPragma {
    const NAME: &'static str = "table_xinfo";
    type Scope = PerSchema;
}

/// A query for ordinary columns from `PRAGMA table_info`.
#[derive(Debug)]
pub struct TableInfoQuery<'a> {
    query: PragmaQuery<'a, TableInfoPragma>,
}

/// A query for ordinary, hidden, and generated columns from `PRAGMA table_xinfo`.
#[derive(Debug)]
pub struct TableXInfoQuery<'a> {
    query: PragmaQuery<'a, TableXInfoPragma>,
}

/// Reports ordinary columns through `PRAGMA table_info` in the named schema, or through unqualified lookup with temporary-table shadowing for `None`.
///
/// ```rust
/// # include!("../../doctest_setup.rs");
/// use diesel::connection::SimpleConnection;
/// use diesel::sqlite::pragma::{table_info, TableColumnInfo, TableColumnKind};
///
/// # fn main() -> QueryResult<()> {
/// let conn = &mut SqliteConnection::establish(":memory:").unwrap();
/// conn.batch_execute(
///     "CREATE TABLE books (id INTEGER PRIMARY KEY, title TEXT NOT NULL DEFAULT 'untitled')"
/// )?;
///
/// let columns = table_info("books", None).load::<TableColumnInfo>(conn)?;
/// assert_eq!(
///     columns
///         .iter()
///         .map(|column| (column.name.as_str(), column.kind))
///         .collect::<Vec<_>>(),
///     [("id", TableColumnKind::Normal), ("title", TableColumnKind::Normal)],
/// );
/// assert_eq!(core::num::NonZeroU32::new(1), columns[0].primary_key_position);
/// assert_eq!(columns[1].default_value.as_deref(), Some("'untitled'"));
/// assert!(columns[1].not_null);
/// # Ok(())
/// # }
/// ```
pub fn table_info<'a>(table: &'a str, schema: Option<&'a str>) -> TableInfoQuery<'a> {
    TableInfoQuery {
        query: PragmaQuery::new(schema, Some(PragmaLiteral::Text(table))),
    }
}

/// Reports ordinary, hidden, and generated columns through `PRAGMA table_xinfo` on SQLite 3.26 or later, with the schema lookup of [`table_info`].
pub fn table_xinfo<'a>(table: &'a str, schema: Option<&'a str>) -> TableXInfoQuery<'a> {
    TableXInfoQuery {
        query: PragmaQuery::new(schema, Some(PragmaLiteral::Text(table))),
    }
}

impl QueryFragment<Sqlite> for TableInfoQuery<'_> {
    fn walk_ast<'b>(&'b self, mut out: AstPass<'_, 'b, Sqlite>) -> QueryResult<()> {
        out.unsafe_to_cache_prepared();
        self.query.walk_ast(out)
    }
}

impl Query for TableInfoQuery<'_> {
    type SqlType = TableInfoSqlType;
}

impl QueryId for TableInfoQuery<'_> {
    type QueryId = ();

    const HAS_STATIC_QUERY_ID: bool = false;
}

impl RunQueryDslSupport for TableInfoQuery<'_> {}

impl QueryFragment<Sqlite> for TableXInfoQuery<'_> {
    fn walk_ast<'b>(&'b self, mut out: AstPass<'_, 'b, Sqlite>) -> QueryResult<()> {
        out.unsafe_to_cache_prepared();
        self.query.walk_ast(out)
    }
}

impl Query for TableXInfoQuery<'_> {
    type SqlType = TableXInfoSqlType;
}

impl QueryId for TableXInfoQuery<'_> {
    type QueryId = ();

    const HAS_STATIC_QUERY_ID: bool = false;
}

impl RunQueryDslSupport for TableXInfoQuery<'_> {}

/// The kind of a column as reported by `PRAGMA table_xinfo`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TableColumnKind {
    /// An ordinary column of the table schema.
    Normal,
    /// A hidden virtual-table column.
    Hidden,
    /// A generated column that is computed whenever it is read.
    VirtualGenerated,
    /// A generated column whose value is stored in the table.
    StoredGenerated,
}

impl TableColumnKind {
    fn from_hidden(hidden: i32) -> Result<Self> {
        match hidden {
            0 => Ok(Self::Normal),
            1 => Ok(Self::Hidden),
            2 => Ok(Self::VirtualGenerated),
            3 => Ok(Self::StoredGenerated),
            _ => Err(alloc::format!("unrecognized `table_xinfo` hidden flag {hidden}").into()),
        }
    }
}

/// Column metadata from `PRAGMA table_info` or `PRAGMA table_xinfo`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TableColumnInfo {
    /// The zero-based rank of the column within the rows the pragma returns.
    pub cid: u32,
    /// The name of the column.
    pub name: String,
    /// The declared type of the column, empty when it declares none.
    pub type_name: String,
    /// Whether SQLite reports the column as `NOT NULL`.
    pub not_null: bool,
    /// SQLite's SQL default expression, with `None` for no default and `Some("NULL")` for `DEFAULT NULL`.
    pub default_value: Option<String>,
    /// The one-based primary-key position, or `None` for a non-key column.
    pub primary_key_position: Option<NonZeroU32>,
    /// The column kind, always [`TableColumnKind::Normal`] for `table_info`.
    pub kind: TableColumnKind,
}

type InfoRow = (i32, String, String, bool, Option<String>, i32);
type XInfoRow = (i32, String, String, bool, Option<String>, i32, i32);

impl Queryable<TableInfoSqlType, Sqlite> for TableColumnInfo {
    type Row = InfoRow;

    fn build(row: Self::Row) -> Result<Self> {
        build_info(
            row.0,
            row.1,
            row.2,
            row.3,
            row.4,
            row.5,
            TableColumnKind::Normal,
        )
    }
}

impl Queryable<TableXInfoSqlType, Sqlite> for TableColumnInfo {
    type Row = XInfoRow;

    fn build(row: Self::Row) -> Result<Self> {
        let kind = TableColumnKind::from_hidden(row.6)?;
        build_info(row.0, row.1, row.2, row.3, row.4, row.5, kind)
    }
}

fn build_info(
    cid: i32,
    name: String,
    type_name: String,
    not_null: bool,
    default_value: Option<String>,
    primary_key: i32,
    kind: TableColumnKind,
) -> Result<TableColumnInfo> {
    let cid = u32::try_from(cid).map_err(|_| alloc::format!("negative column rank {cid}"))?;
    let primary_key_position = NonZeroU32::new(
        u32::try_from(primary_key)
            .map_err(|_| alloc::format!("invalid primary key position {primary_key}"))?,
    );
    Ok(TableColumnInfo {
        cid,
        name,
        type_name,
        not_null,
        default_value,
        primary_key_position,
        kind,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::connection::{DatabaseVersion, SimpleConnection};
    use crate::prelude::*;
    use crate::sqlite::SqliteConnection;

    fn connection() -> SqliteConnection {
        SqliteConnection::establish(":memory:").unwrap()
    }

    const PLAIN_TABLE: &str = "CREATE TABLE metadata (
        seeded TEXT NOT NULL DEFAULT 'seed',
        nulled TEXT DEFAULT NULL,
        plain TEXT,
        key_a TEXT,
        key_b TEXT,
        PRIMARY KEY (key_b, key_a)
    )";

    #[diesel_test_helper::test]
    fn table_info_reports_ranks_defaults_and_composite_key_ordinals() {
        let conn = &mut connection();
        conn.batch_execute(PLAIN_TABLE).unwrap();
        let has_xinfo = conn.version() >= DatabaseVersion::new(3, 26, 0);

        for columns in [
            Some(table_info("metadata", None).load::<TableColumnInfo>(conn)),
            has_xinfo.then(|| table_xinfo("metadata", None).load::<TableColumnInfo>(conn)),
        ]
        .into_iter()
        .flatten()
        {
            let columns = columns.unwrap();
            assert_eq!(
                columns
                    .iter()
                    .map(|column| (column.name.as_str(), column.kind))
                    .collect::<Vec<_>>(),
                [
                    ("seeded", TableColumnKind::Normal),
                    ("nulled", TableColumnKind::Normal),
                    ("plain", TableColumnKind::Normal),
                    ("key_a", TableColumnKind::Normal),
                    ("key_b", TableColumnKind::Normal),
                ]
            );
            for (rank, column) in columns.iter().enumerate() {
                assert_eq!(u32::try_from(rank).unwrap(), column.cid);
            }
            assert_eq!(columns[0].type_name, "TEXT");
            assert!(columns[0].not_null);
            assert_eq!(columns[0].default_value.as_deref(), Some("'seed'"));
            assert_eq!(columns[1].default_value.as_deref(), Some("NULL"));
            assert_eq!(columns[2].default_value, None);
            assert!(!columns[2].not_null);
            assert_eq!(columns[0].primary_key_position, None);
            assert_eq!(columns[3].primary_key_position, NonZeroU32::new(2));
            assert_eq!(columns[4].primary_key_position, NonZeroU32::new(1));
        }
    }

    #[diesel_test_helper::test]
    fn absent_table_reports_no_columns() {
        let conn = &mut connection();
        let has_xinfo = conn.version() >= DatabaseVersion::new(3, 26, 0);
        for result in [
            Some(table_info("no_such_table", None).load::<TableColumnInfo>(conn)),
            has_xinfo.then(|| table_xinfo("no_such_table", None).load::<TableColumnInfo>(conn)),
        ]
        .into_iter()
        .flatten()
        {
            assert_eq!(Vec::<TableColumnInfo>::new(), result.unwrap());
        }
    }

    #[diesel_test_helper::test]
    fn xinfo_classifies_generated_columns_and_table_info_skips_them() {
        let conn = &mut connection();
        if conn.version() < DatabaseVersion::new(3, 31, 0) {
            return;
        }
        conn.batch_execute(
            "CREATE TABLE metadata (
                first INTEGER,
                computed INTEGER GENERATED ALWAYS AS (first + 1),
                stored INTEGER GENERATED ALWAYS AS (first * 3) STORED,
                last TEXT
            )",
        )
        .unwrap();

        let columns = table_xinfo("metadata", None)
            .load::<TableColumnInfo>(conn)
            .unwrap();
        assert_eq!(
            columns
                .iter()
                .map(|column| (column.name.as_str(), column.kind))
                .collect::<Vec<_>>(),
            [
                ("first", TableColumnKind::Normal),
                ("computed", TableColumnKind::VirtualGenerated),
                ("stored", TableColumnKind::StoredGenerated),
                ("last", TableColumnKind::Normal),
            ]
        );
        assert_eq!(columns[1].type_name, "INTEGER");

        let visible = table_info("metadata", None)
            .load::<TableColumnInfo>(conn)
            .unwrap();
        assert_eq!(
            visible
                .iter()
                .map(|column| (column.name.as_str(), column.cid, column.kind))
                .collect::<Vec<_>>(),
            [
                ("first", 0, TableColumnKind::Normal),
                ("last", 1, TableColumnKind::Normal),
            ]
        );
    }

    #[diesel_test_helper::test]
    fn xinfo_reports_the_pragma_virtual_table_argument_columns_as_hidden() {
        let conn = &mut connection();
        if conn.version() < DatabaseVersion::new(3, 26, 0) {
            return;
        }
        let columns = table_xinfo("pragma_table_info", None)
            .load::<TableColumnInfo>(conn)
            .unwrap();
        let argument = columns.iter().find(|column| column.name == "arg").unwrap();
        assert_eq!(argument.kind, TableColumnKind::Hidden);
        assert_eq!(argument.type_name, "");

        let visible = table_info("pragma_table_info", None)
            .load::<TableColumnInfo>(conn)
            .unwrap();
        assert!(!visible.iter().any(|column| column.name == "arg"));
    }

    #[diesel_test_helper::test]
    fn metadata_rejects_invalid_ranks_key_positions_and_kinds() {
        let conn = &mut connection();
        for (cid, primary_key, hidden) in [(-1, 0, 0), (0, -1, 0), (0, 0, 4)] {
            let result = crate::select((
                cid.into_sql::<Integer>(),
                "column".into_sql::<Text>(),
                "".into_sql::<Text>(),
                false.into_sql::<Bool>(),
                None::<String>.into_sql::<Nullable<Text>>(),
                primary_key.into_sql::<Integer>(),
                hidden.into_sql::<Integer>(),
            ))
            .get_result::<TableColumnInfo>(conn);
            assert!(matches!(
                result,
                Err(crate::result::Error::DeserializationError(_))
            ));
        }
    }
}
