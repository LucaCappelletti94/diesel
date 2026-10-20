use std::collections::HashMap;

use diesel::connection::DatabaseVersion;
use diesel::deserialize::FromSqlRow;
use diesel::dsl::sql;
use diesel::row::{NamedRow, Row};
use diesel::sql_types::{Bool, Integer, Text};
use diesel::sqlite::Sqlite;
use diesel::sqlite::pragma::{TableInfoSqlType, TableXInfoSqlType, table_info, table_xinfo};
use diesel::*;

use super::data_structures::*;
use super::table_data::TableName;
use crate::config::PrintSchema;
use crate::print_schema::ColumnSorting;

table! {
    sqlite_master (name) {
        name -> VarChar,
        sql -> VarChar,
        #[sql_name = "type"]
        tpe -> VarChar,
    }
}

table! {
    pragma_foreign_key_list {
        id -> Integer,
        seq -> Integer,
        _table -> VarChar,
        from -> VarChar,
        to -> Nullable<VarChar>,
        on_update -> VarChar,
        on_delete -> VarChar,
        _match -> VarChar,
    }
}

fn escape_identifier(identifier: &str) -> String {
    identifier.replace('\'', "''")
}

pub fn load_table_names(
    connection: &mut SqliteConnection,
    schema_name: Option<&str>,
) -> Result<Vec<(SupportedQueryRelationStructures, TableName)>, crate::errors::Error> {
    use self::sqlite_master::dsl::*;

    if schema_name.is_some() {
        return Err(crate::errors::Error::InvalidSqliteSchema);
    }
    let tables = sqlite_master
        .select(name)
        .filter(name.not_like("\\_\\_%").escape('\\'))
        .filter(name.not_like("sqlite%"))
        .filter(tpe.eq("table"))
        .order(name)
        .load::<String>(connection)?
        .into_iter()
        .map(|table| {
            (
                SupportedQueryRelationStructures::Table,
                TableName::from_name(table),
            )
        });
    let view = sqlite_master
        .select(name)
        .filter(name.not_like("\\_\\_%").escape('\\'))
        .filter(name.not_like("sqlite%"))
        .filter(tpe.eq("view"))
        .order(name)
        .load::<String>(connection)?
        .into_iter()
        .map(|table| {
            (
                SupportedQueryRelationStructures::View,
                TableName::from_name(table),
            )
        });

    Ok(tables.chain(view).collect())
}

pub fn load_foreign_key_constraints(
    connection: &mut SqliteConnection,
    schema_name: Option<&str>,
) -> Result<Vec<ForeignKeyConstraint>, crate::errors::Error> {
    let tables = load_table_names(connection, schema_name)?;
    let rows = tables
        .into_iter()
        .map(|(_, child_table)| {
            let query = format!(
                "PRAGMA FOREIGN_KEY_LIST('{}')",
                escape_identifier(&child_table.sql_name)
            );
            sql::<pragma_foreign_key_list::SqlType>(&query)
                .load::<ForeignKeyListRow>(connection)?
                .into_iter()
                .map(|row| {
                    let parent_table = TableName::from_name(row.parent_table);
                    let primary_key = if let Some(primary_key) = row.primary_key {
                        vec![primary_key]
                    } else {
                        get_primary_keys(connection, &parent_table)?
                    };
                    let foreign_key_columns_rust = super::inference::rust_name_for_sql_name(
                        &row.foreign_key,
                        Some(&child_table),
                    );
                    Ok(ForeignKeyConstraint {
                        child_table: child_table.clone(),
                        parent_table,
                        foreign_key_columns: vec![row.foreign_key.clone()],
                        foreign_key_columns_rust: vec![foreign_key_columns_rust],
                        primary_key_columns: primary_key,
                    })
                })
                .collect::<Result<_, _>>()
        })
        .collect::<QueryResult<Vec<Vec<_>>>>()?;
    Ok(rows.into_iter().flatten().collect())
}

// Default to `Integer` so inferred foreign-key types agree.
const ROWID_TYPE_NAME: &str = "Integer";

pub fn get_table_data(
    conn: &mut SqliteConnection,
    table: &TableName,
    column_sorting: &ColumnSorting,
    kind: SupportedQueryRelationStructures,
) -> QueryResult<Vec<ColumnInformation>> {
    let mut columns = if conn.version() >= DatabaseVersion::new(3, 26, 0) {
        // Generated columns require the extended metadata query.
        table_xinfo(&table.sql_name, None).load::<TableMetadataColumn>(conn)?
    } else {
        table_info(&table.sql_name, None).load::<TableMetadataColumn>(conn)?
    };
    if matches!(kind, SupportedQueryRelationStructures::Table)
        && !columns.iter().any(|column| column.primary_key)
        && let Some(alias) = implicit_rowid_alias(
            columns
                .iter()
                .map(|column| column.column_information.column_name.as_str()),
        )
    {
        columns.insert(
            0,
            TableMetadataColumn {
                column_information: ColumnInformation::new(
                    alias.to_owned(),
                    ROWID_TYPE_NAME,
                    None,
                    false,
                    None,
                    None,
                    false,
                ),
                primary_key: true,
            },
        );
    }

    match column_sorting {
        ColumnSorting::OrdinalPosition => {}
        ColumnSorting::Name => {
            columns.sort_by(|a, b| {
                a.column_information
                    .column_name
                    .cmp(&b.column_information.column_name)
            });
        }
    };
    Ok(columns
        .into_iter()
        .map(|column| column.column_information)
        .collect())
}

struct TableMetadataColumn {
    column_information: ColumnInformation,
    primary_key: bool,
}

impl TableMetadataColumn {
    fn decode<'a>(row: &impl Row<'a, Sqlite>) -> deserialize::Result<Self> {
        let column_name = row.get_value::<Text, String, _>(1)?;
        let type_name = row.get_value::<Text, String, _>(2)?;
        let notnull = row.get_value::<Bool, bool, _>(3)?;
        let primary_key = row.get_value::<Integer, i32, _>(5)? != 0;

        Ok(Self {
            column_information: ColumnInformation::new(
                column_name,
                type_name,
                None,
                !notnull,
                None,
                None,
                false,
            ),
            primary_key,
        })
    }
}

impl FromSqlRow<TableInfoSqlType, Sqlite> for TableMetadataColumn {
    fn build_from_row<'a>(row: &impl Row<'a, Sqlite>) -> deserialize::Result<Self> {
        Self::decode(row)
    }
}

impl FromSqlRow<TableXInfoSqlType, Sqlite> for TableMetadataColumn {
    fn build_from_row<'a>(row: &impl Row<'a, Sqlite>) -> deserialize::Result<Self> {
        Self::decode(row)
    }
}

struct PrimaryKeyInformation {
    name: String,
    primary_key: bool,
}

impl PrimaryKeyInformation {
    fn decode<'a>(row: &impl Row<'a, Sqlite>) -> deserialize::Result<Self> {
        Ok(Self {
            name: row.get_value::<Text, String, _>(1)?,
            primary_key: row.get_value::<Integer, i32, _>(5)? != 0,
        })
    }
}

impl FromSqlRow<TableInfoSqlType, Sqlite> for PrimaryKeyInformation {
    fn build_from_row<'a>(row: &impl Row<'a, Sqlite>) -> deserialize::Result<Self> {
        Self::decode(row)
    }
}

impl FromSqlRow<TableXInfoSqlType, Sqlite> for PrimaryKeyInformation {
    fn build_from_row<'a>(row: &impl Row<'a, Sqlite>) -> deserialize::Result<Self> {
        Self::decode(row)
    }
}

struct WithoutRowIdInformation {
    name: String,
    without_row_id: bool,
}

impl QueryableByName<Sqlite> for WithoutRowIdInformation {
    fn build<'a>(row: &impl NamedRow<'a, Sqlite>) -> deserialize::Result<Self> {
        Ok(Self {
            name: NamedRow::get::<Text, String>(row, "name")?,
            without_row_id: NamedRow::get::<Bool, bool>(row, "wr")?,
        })
    }
}

pub fn column_is_row_id(
    conn: &mut SqliteConnection,
    table: &TableName,
    primary_keys: Option<&[String]>,
    column_name: &str,
    type_name: &str,
) -> Result<bool, crate::errors::Error> {
    let sqlite_version = conn.version();
    if sqlite_version < DatabaseVersion::new(3, 37, 0) {
        return Err(crate::errors::Error::UnsupportedFeature(format!(
            "Parameter `sqlite_integer_primary_key_is_bigint` needs SQLite 3.37 or above. \
            Your current SQLite version is {sqlite_version}."
        )));
    }

    if type_name != "integer" {
        return Ok(false);
    }

    if !matches!(primary_keys, Some([pk]) if pk == column_name) {
        return Ok(false);
    }

    let table_list_query = format!(
        "PRAGMA TABLE_LIST('{}')",
        escape_identifier(&table.sql_name)
    );
    let table_list_results = sql_query(table_list_query).load::<WithoutRowIdInformation>(conn)?;

    let res = table_list_results
        .iter()
        .find(|wr_info| wr_info.name == table.sql_name)
        .map(|wr_info| !wr_info.without_row_id)
        .unwrap_or_default();

    Ok(res)
}

#[derive(Queryable)]
struct ForeignKeyListRow {
    _id: i32,
    _seq: i32,
    parent_table: String,
    foreign_key: String,
    primary_key: Option<String>,
    _on_update: String,
    _on_delete: String,
    _match: String,
}

/// SQLite `rowid` aliases in fallback preference order.
const SQLITE_ROWID_ALIASES: &[&str] = &["rowid", "oid", "_rowid_"];

pub fn get_primary_keys(
    conn: &mut SqliteConnection,
    table: &TableName,
) -> QueryResult<Vec<String>> {
    let results = if conn.version() >= DatabaseVersion::new(3, 26, 0) {
        table_xinfo(&table.sql_name, None).load::<PrimaryKeyInformation>(conn)?
    } else {
        table_info(&table.sql_name, None).load::<PrimaryKeyInformation>(conn)?
    };
    if results.iter().any(|row| row.primary_key) {
        Ok(results
            .into_iter()
            .filter(|row| row.primary_key)
            .map(|row| row.name)
            .collect())
    } else {
        // Declared columns shadow SQLite's implicit `rowid` aliases.
        Ok(
            implicit_rowid_alias(results.iter().map(|row| row.name.as_str()))
                .into_iter()
                .map(str::to_owned)
                .collect(),
        )
    }
}

fn implicit_rowid_alias<'a>(
    column_names: impl Iterator<Item = &'a str> + Clone,
) -> Option<&'static str> {
    SQLITE_ROWID_ALIASES
        .iter()
        .copied()
        .find(|alias| !column_names.clone().any(|name| name == *alias))
}

#[tracing::instrument(skip(conn))]
pub fn determine_column_type(
    conn: &mut SqliteConnection,
    attr: &ColumnInformation,
    table: &TableName,
    primary_keys: Option<&[String]>,
    foreign_keys: &HashMap<String, ForeignKeyConstraint>,
    config: &PrintSchema,
) -> Result<ColumnType, crate::errors::Error> {
    let mut type_name = attr.type_name.to_lowercase();
    if type_name == "generated always" {
        type_name.clear();
    }

    let path = if is_bool(&type_name) {
        String::from("Bool")
    } else if is_smallint(&type_name) {
        String::from("SmallInt")
    } else if is_bigint(&type_name) {
        String::from("BigInt")
    } else if type_name.contains("int") {
        let sqlite_integer_primary_key_is_bigint = config
            .sqlite_integer_primary_key_is_bigint
            .unwrap_or_default();

        if sqlite_integer_primary_key_is_bigint
            && (column_is_row_id(conn, table, primary_keys, &attr.column_name, &type_name)?
                || column_references_row_id(foreign_keys.get(&attr.column_name), conn)?)
        {
            String::from("BigInt")
        } else {
            String::from("Integer")
        }
    } else if is_text(&type_name) {
        String::from("Text")
    } else if is_binary(&type_name) {
        String::from("Binary")
    } else if is_float(&type_name) {
        String::from("Float")
    } else if is_double(&type_name) {
        String::from("Double")
    } else if type_name == "datetime" || type_name == "timestamp" {
        String::from("Timestamp")
    } else if type_name == "date" {
        String::from("Date")
    } else if type_name == "time" {
        String::from("Time")
    } else {
        return Err(crate::errors::Error::UnsupportedType(type_name));
    };

    Ok(ColumnType {
        schema: None,
        rust_name: path.clone(),
        sql_name: path,
        is_array: false,
        is_nullable: attr.nullable,
        is_unsigned: false,
        record: None,
        max_length: attr.max_length,
        unmodified_type: attr.type_name.to_owned(),
    })
}

fn column_references_row_id(
    foreign_constraint: Option<&ForeignKeyConstraint>,
    conn: &mut SqliteConnection,
) -> Result<bool, crate::errors::Error> {
    if let Some(foreign_constraint) = foreign_constraint {
        let parent_primary_keys = get_primary_keys(conn, &foreign_constraint.parent_table)?;
        if let [id] = parent_primary_keys.as_slice() {
            column_is_row_id(
                conn,
                &foreign_constraint.parent_table,
                Some(&parent_primary_keys),
                id,
                "integer",
            )
        } else {
            Ok(false)
        }
    } else {
        Ok(false)
    }
}

fn is_text(type_name: &str) -> bool {
    type_name.contains("char") || type_name.contains("clob") || type_name.contains("text")
}

fn is_binary(type_name: &str) -> bool {
    type_name.contains("blob") || type_name.contains("binary") || type_name.is_empty()
}

fn is_bool(type_name: &str) -> bool {
    type_name == "boolean"
        || type_name == "bool"
        || type_name.contains("tiny") && type_name.contains("int")
}

fn is_smallint(type_name: &str) -> bool {
    type_name == "int2" || type_name.contains("small") && type_name.contains("int")
}

fn is_bigint(type_name: &str) -> bool {
    type_name == "int8" || type_name.contains("big") && type_name.contains("int")
}

fn is_float(type_name: &str) -> bool {
    type_name.contains("float") || type_name.contains("real")
}

fn is_double(type_name: &str) -> bool {
    type_name.contains("double") || type_name.contains("num") || type_name.contains("dec")
}

pub(crate) fn load_view_sql_definition(
    sqlite_connection: &mut SqliteConnection,
    name: &TableName,
) -> Result<String, crate::errors::Error> {
    sqlite_master::table
        .filter(sqlite_master::name.eq(&name.sql_name))
        .select(sqlite_master::sql)
        .get_result::<String>(sqlite_connection)
        .map_err(crate::errors::Error::from)
}

#[test]
fn load_table_names_returns_nothing_when_no_tables_exist() {
    let mut conn = SqliteConnection::establish(":memory:").unwrap();
    assert_eq!(
        Vec::<TableName>::new(),
        load_table_names(&mut conn, None)
            .unwrap()
            .into_iter()
            .map(|(_, table)| table)
            .collect::<Vec<_>>()
    );
}

#[test]
fn load_table_names_includes_tables_that_exist() {
    let mut conn = SqliteConnection::establish(":memory:").unwrap();
    diesel::sql_query("CREATE TABLE users (id INTEGER PRIMARY KEY AUTOINCREMENT)")
        .execute(&mut conn)
        .unwrap();
    let table_names = load_table_names(&mut conn, None)
        .unwrap()
        .into_iter()
        .map(|(_, table)| table)
        .collect::<Vec<_>>();
    assert!(table_names.contains(&TableName::from_name("users")));
}

#[test]
fn load_table_names_excludes_diesel_metadata_tables() {
    let mut conn = SqliteConnection::establish(":memory:").unwrap();
    diesel::sql_query("CREATE TABLE __diesel_metadata (id INTEGER PRIMARY KEY AUTOINCREMENT)")
        .execute(&mut conn)
        .unwrap();
    let table_names = load_table_names(&mut conn, None)
        .unwrap()
        .into_iter()
        .map(|(_, table)| table)
        .collect::<Vec<_>>();
    assert!(!table_names.contains(&TableName::from_name("__diesel_metadata")));
}

#[test]
fn load_table_names_excludes_sqlite_metadata_tables() {
    let mut conn = SqliteConnection::establish(":memory:").unwrap();
    diesel::sql_query("CREATE TABLE __diesel_metadata (id INTEGER PRIMARY KEY AUTOINCREMENT)")
        .execute(&mut conn)
        .unwrap();
    diesel::sql_query("CREATE TABLE users (id INTEGER PRIMARY KEY AUTOINCREMENT)")
        .execute(&mut conn)
        .unwrap();
    let table_names = load_table_names(&mut conn, None)
        .unwrap()
        .into_iter()
        .map(|(_, table)| table)
        .collect::<Vec<_>>();
    assert_eq!(vec![TableName::from_name("users")], table_names);
}

#[test]
fn load_table_names_includes_views() {
    let mut conn = SqliteConnection::establish(":memory:").unwrap();
    diesel::sql_query("CREATE TABLE users (id INTEGER PRIMARY KEY AUTOINCREMENT)")
        .execute(&mut conn)
        .unwrap();
    diesel::sql_query("CREATE VIEW answer AS SELECT 42")
        .execute(&mut conn)
        .unwrap();
    let table_names = load_table_names(&mut conn, None)
        .unwrap()
        .into_iter()
        .map(|(_, table)| table)
        .collect::<Vec<_>>();
    assert_eq!(
        vec![
            TableName::from_name("users"),
            TableName::from_name("answer")
        ],
        table_names
    );
}

#[test]
fn load_table_names_returns_error_when_given_schema_name() {
    let mut conn = SqliteConnection::establish(":memory:").unwrap();
    // We're testing the error message rather than using #[should_panic]
    // to ensure this is returning an error and not actually panicking.
    let table_names = load_table_names(&mut conn, Some("stuff"));
    match table_names {
        Ok(_) => panic!("Expected load_table_names to return an error"),
        Err(e) => assert!(e.to_string().starts_with(
            "sqlite cannot infer \
             schema for databases"
        )),
    }
}

#[test]
fn load_table_names_output_is_ordered() {
    let mut conn = SqliteConnection::establish(":memory:").unwrap();
    diesel::sql_query("CREATE TABLE bbb (id INTEGER PRIMARY KEY AUTOINCREMENT)")
        .execute(&mut conn)
        .unwrap();
    diesel::sql_query("CREATE TABLE aaa (id INTEGER PRIMARY KEY AUTOINCREMENT)")
        .execute(&mut conn)
        .unwrap();
    diesel::sql_query("CREATE TABLE ccc (id INTEGER PRIMARY KEY AUTOINCREMENT)")
        .execute(&mut conn)
        .unwrap();

    let table_names = load_table_names(&mut conn, None)
        .unwrap()
        .iter()
        .map(|(_, table)| table.to_string())
        .collect::<Vec<_>>();
    assert_eq!(vec!["aaa", "bbb", "ccc"], table_names);
}

#[test]
fn load_foreign_key_constraints_loads_foreign_keys() {
    let mut connection = SqliteConnection::establish(":memory:").unwrap();

    diesel::sql_query("CREATE TABLE table_1 (id)")
        .execute(&mut connection)
        .unwrap();
    diesel::sql_query("CREATE TABLE table_2 (id, fk_one REFERENCES table_1(id))")
        .execute(&mut connection)
        .unwrap();
    diesel::sql_query("CREATE TABLE table_3 (id, fk_two REFERENCES table_2(id))")
        .execute(&mut connection)
        .unwrap();

    let table_1 = TableName::from_name("table_1");
    let table_2 = TableName::from_name("table_2");
    let table_3 = TableName::from_name("table_3");
    let fk_one = ForeignKeyConstraint {
        child_table: table_2.clone(),
        parent_table: table_1,
        foreign_key_columns: vec!["fk_one".into()],
        foreign_key_columns_rust: vec!["fk_one".into()],
        primary_key_columns: vec!["id".into()],
    };
    let fk_two = ForeignKeyConstraint {
        child_table: table_3,
        parent_table: table_2,
        foreign_key_columns: vec!["fk_two".into()],
        foreign_key_columns_rust: vec!["fk_two".into()],
        primary_key_columns: vec!["id".into()],
    };

    let fks = load_foreign_key_constraints(&mut connection, None).unwrap();
    assert_eq!(vec![fk_one, fk_two], fks);
}

#[test]
fn all_rowid_aliases_used_empty_result() {
    let mut connection = SqliteConnection::establish(":memory:").unwrap();

    diesel::sql_query("CREATE TABLE table_1 (rowid TEXT, oid TEXT, _rowid_ TEXT)")
        .execute(&mut connection)
        .unwrap();

    let table_1 = TableName::from_name("table_1");

    let res = get_primary_keys(&mut connection, &table_1);
    assert!(res.is_ok());
    assert!(res.unwrap().is_empty());
}

#[test]
fn integer_primary_key_sqlite_3_37() {
    let mut conn = SqliteConnection::establish(":memory:").unwrap();

    if conn.version() < DatabaseVersion::new(3, 37, 0) {
        return;
    }

    let test_data = [
        (
            "table_1",
            "CREATE TABLE table_1 (id INTEGER PRIMARY KEY)",
            vec![("id", "Integer".to_owned())],
            vec![("id", "BigInt".to_owned())],
        ),
        (
            "table_2",
            "CREATE TABLE table_2 (id INTEGER, PRIMARY KEY(id))",
            vec![("id", "Integer".to_owned())],
            vec![("id", "BigInt".to_owned())],
        ),
        (
            "table_3",
            "CREATE TABLE table_3 (id INTEGER)",
            vec![
                ("rowid", "Integer".to_owned()),
                ("id", "Integer".to_owned()),
            ],
            vec![("rowid", "BigInt".to_owned()), ("id", "Integer".to_owned())],
        ),
        (
            "table_4",
            "CREATE TABLE table_4 (id1 INTEGER, id2 INTEGER, PRIMARY KEY(id1, id2))",
            vec![("id1", "Integer".to_owned()), ("id2", "Integer".to_owned())],
            vec![("id1", "Integer".to_owned()), ("id2", "Integer".to_owned())],
        ),
        (
            "table_5",
            "CREATE TABLE table_5 (id INT PRIMARY KEY)",
            vec![("id", "Integer".to_owned())],
            vec![("id", "Integer".to_owned())],
        ),
        (
            "table_6",
            "CREATE TABLE table_6 (id INTEGER PRIMARY KEY) WITHOUT ROWID",
            vec![("id", "Integer".to_owned())],
            vec![("id", "Integer".to_owned())],
        ),
    ];

    for (table_name, sql_query, expected_off_types, expected_on_types) in test_data {
        diesel::sql_query(sql_query).execute(&mut conn).unwrap();

        let table = TableName::from_name(table_name);
        let column_infos = get_table_data(
            &mut conn,
            &table,
            &Default::default(),
            SupportedQueryRelationStructures::Table,
        )
        .unwrap();

        let primary_keys = get_primary_keys(&mut conn, &table).unwrap();

        let off_column_types = column_infos
            .iter()
            .map(|column_info| {
                (
                    column_info.column_name.as_str(),
                    determine_column_type(
                        &mut conn,
                        column_info,
                        &table,
                        Some(&primary_keys),
                        &HashMap::new(),
                        &Default::default(),
                    )
                    .unwrap()
                    .sql_name,
                )
            })
            .collect::<Vec<_>>();

        let on_column_types = column_infos
            .iter()
            .map(|column_info| {
                (
                    column_info.column_name.as_str(),
                    determine_column_type(
                        &mut conn,
                        column_info,
                        &table,
                        Some(&primary_keys),
                        &HashMap::new(),
                        &PrintSchema {
                            sqlite_integer_primary_key_is_bigint: Some(true),
                            ..Default::default()
                        },
                    )
                    .unwrap()
                    .sql_name,
                )
            })
            .collect::<Vec<_>>();

        assert_eq!(
            (table_name, off_column_types),
            (table_name, expected_off_types)
        );

        assert_eq!(
            (table_name, on_column_types),
            (table_name, expected_on_types)
        );
    }
}

#[test]
fn metadata_decoders_accept_both_result_shapes() {
    let mut conn = SqliteConnection::establish(":memory:").unwrap();
    let has_xinfo = conn.version() >= DatabaseVersion::new(3, 26, 0);
    let has_generated = conn.version() >= DatabaseVersion::new(3, 31, 0);

    diesel::sql_query(
        "CREATE TABLE metadata_table (
            id INTEGER PRIMARY KEY,
            other_id INTEGER NOT NULL,
            default_col TEXT DEFAULT 'unused default'
        )",
    )
    .execute(&mut conn)
    .unwrap();
    if has_generated {
        diesel::sql_query(
            "ALTER TABLE metadata_table ADD COLUMN generated_col INTEGER GENERATED ALWAYS AS (other_id * 2)",
        )
        .execute(&mut conn)
        .unwrap();
    }

    let expected_columns = [
        ("id", "INTEGER", true, true),
        ("other_id", "INTEGER", false, false),
        ("default_col", "TEXT", true, false),
        ("generated_col", "INTEGER", true, false),
    ];

    for (columns, expected) in [
        Some((
            table_info("metadata_table", None)
                .load::<TableMetadataColumn>(&mut conn)
                .unwrap(),
            &expected_columns[..3],
        )),
        has_xinfo.then(|| {
            (
                table_xinfo("metadata_table", None)
                    .load::<TableMetadataColumn>(&mut conn)
                    .unwrap(),
                &expected_columns[..if has_generated { 4 } else { 3 }],
            )
        }),
    ]
    .into_iter()
    .flatten()
    {
        assert_eq!(
            columns
                .iter()
                .map(|column| {
                    (
                        column.column_information.column_name.as_str(),
                        column.column_information.type_name.as_str(),
                        column.column_information.nullable,
                        column.primary_key,
                    )
                })
                .collect::<Vec<_>>(),
            expected,
        );
    }

    diesel::sql_query(
        "CREATE TABLE composite_table (
            id1 INTEGER,
            id2 INTEGER,
            PRIMARY KEY (id2, id1)
        )",
    )
    .execute(&mut conn)
    .unwrap();

    assert_eq!(
        get_primary_keys(&mut conn, &TableName::from_name("composite_table")).unwrap(),
        vec!["id1".to_owned(), "id2".to_owned()],
    );

    for rows in [
        Some(
            table_info("composite_table", None)
                .load::<PrimaryKeyInformation>(&mut conn)
                .unwrap(),
        ),
        has_xinfo.then(|| {
            table_xinfo("composite_table", None)
                .load::<PrimaryKeyInformation>(&mut conn)
                .unwrap()
        }),
    ]
    .into_iter()
    .flatten()
    {
        assert_eq!(
            rows.iter()
                .map(|row| (row.name.as_str(), row.primary_key))
                .collect::<Vec<_>>(),
            [("id1", true), ("id2", true)],
        );
    }
}
