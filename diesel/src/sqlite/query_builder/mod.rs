//! The SQLite query builder

use super::backend::Sqlite;
use crate::query_builder::QueryBuilder;
use crate::result::QueryResult;
use alloc::string::String;

mod batch_update;
mod limit_offset;
mod query_fragment_impls;
mod returning;

/// Constructs SQL queries for use with the SQLite backend
#[allow(missing_debug_implementations)]
#[derive(Default)]
pub struct SqliteQueryBuilder {
    sql: String,
}

impl SqliteQueryBuilder {
    /// Construct a new query builder with an empty query
    pub fn new() -> Self {
        SqliteQueryBuilder::default()
    }
}

impl QueryBuilder<Sqlite> for SqliteQueryBuilder {
    fn push_sql(&mut self, sql: &str) {
        self.sql.push_str(sql);
    }

    fn push_identifier(&mut self, identifier: &str) -> QueryResult<()> {
        self.push_sql("`");
        if identifier.contains('`') {
            self.push_sql(&identifier.replace('`', "``"));
        } else {
            self.push_sql(identifier);
        }
        self.push_sql("`");
        Ok(())
    }

    fn push_bind_param(&mut self) {
        self.push_sql("?");
    }

    fn finish(self) -> String {
        self.sql
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[diesel_test_helper::test]
    fn push_identifier_escapes_embedded_backticks() {
        let mut builder = SqliteQueryBuilder::new();
        builder.push_identifier("users").unwrap();
        builder.push_identifier("we`ird").unwrap();
        assert_eq!(builder.finish(), "`users``we``ird`");
    }
}
