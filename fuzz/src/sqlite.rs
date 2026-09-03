//! Sqlite values, reached by binding a parameter and reading the column back.

use diesel::deserialize::FromSqlRow;
use diesel::expression::TypedExpressionType;
use diesel::prelude::*;
use diesel::query_builder::QueryId;
use diesel::sql_types::{Binary, Integer, Jsonb, SingleValue, SqlType, Text};
use std::cell::RefCell;

thread_local! {
    static CONN: RefCell<SqliteConnection> = RefCell::new(
        SqliteConnection::establish(":memory:").expect("an in-memory sqlite database")
    );
}

/// Runs `f` on a thread-local in-memory connection.
pub fn with_conn<R>(f: impl FnOnce(&mut SqliteConnection) -> R) -> R {
    CONN.with(|conn| f(&mut conn.borrow_mut()))
}

/// `SELECT ?` with `blob` bound, decoded by `FromSql<Jsonb, Sqlite>`.
pub fn decode_jsonb(conn: &mut SqliteConnection, blob: &[u8]) -> QueryResult<serde_json::Value> {
    diesel::select(diesel::dsl::sql::<Jsonb>("").bind::<Binary, _>(blob)).get_result(conn)
}

/// `SELECT ?` with `value` bound, encoded by `ToSql<Jsonb, Sqlite>`.
pub fn encode_jsonb(
    conn: &mut SqliteConnection,
    value: &serde_json::Value,
) -> QueryResult<Vec<u8>> {
    diesel::select(diesel::dsl::sql::<Binary>("").bind::<Jsonb, _>(value.clone())).get_result(conn)
}

/// `json_valid(?, 8)`: strict conformance to sqlite's internal JSONB format.
pub fn jsonb_strictly_valid(conn: &mut SqliteConnection, blob: &[u8]) -> bool {
    let valid: i32 = diesel::select(
        diesel::dsl::sql::<Integer>("json_valid(")
            .bind::<Binary, _>(blob)
            .sql(", 8)"),
    )
    .get_result(conn)
    .expect("json_valid accepts any blob");
    valid == 1
}

/// What sqlite makes of a blob, since not every rendering is a
/// `serde_json::Value`.
#[derive(Debug)]
pub enum Oracle {
    Value(serde_json::Value),
    /// A rendering `serde_json` cannot hold, such as a number out of range.
    Unrepresentable(String),
    /// A rendering that is not utf-8, which `serde_json::Value` cannot hold.
    NonUtf8(Vec<u8>),
    /// `json()` refused the blob.
    Failed(String),
}

/// Sqlite's own reading of a blob, through `json()`.
pub fn oracle(conn: &mut SqliteConnection, blob: &[u8]) -> Oracle {
    // as a blob, so invalid UTF-8 is not lost in a lossy cast
    let raw: Vec<u8> = match diesel::select(
        diesel::dsl::sql::<Binary>("json(")
            .bind::<Binary, _>(blob)
            .sql(")"),
    )
    .get_result(conn)
    {
        Ok(raw) => raw,
        Err(error) => return Oracle::Failed(error.to_string()),
    };
    let text = match String::from_utf8(raw) {
        Ok(text) => text,
        Err(error) => return Oracle::NonUtf8(error.into_bytes()),
    };
    match serde_json::from_str(&text) {
        Ok(value) => Oracle::Value(value),
        Err(_) => Oracle::Unrepresentable(text),
    }
}

/// `jsonb(?)`: sqlite's own encoding of json text.
pub fn text_to_jsonb(conn: &mut SqliteConnection, json: &str) -> QueryResult<Vec<u8>> {
    diesel::select(
        diesel::dsl::sql::<Binary>("jsonb(")
            .bind::<Text, _>(json.to_string())
            .sql(")"),
    )
    .get_result(conn)
}

pub fn decode_text_as<ST, T>(conn: &mut SqliteConnection, text: &str) -> QueryResult<T>
where
    ST: SqlType + TypedExpressionType + SingleValue + QueryId,
    diesel::sqlite::Sqlite: diesel::sql_types::HasSqlType<ST>,
    T: FromSqlRow<ST, diesel::sqlite::Sqlite> + 'static,
{
    diesel::select(diesel::dsl::sql::<ST>("").bind::<Text, _>(text.to_string())).get_result(conn)
}
