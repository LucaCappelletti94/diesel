use core::marker::PhantomData;

use crate::backend::Backend;
use crate::query_builder::QueryBuilder;
use crate::result::QueryResult;

#[doc(inline)]
pub use self::query_fragment_impls::DuplicatedKeys;

mod batch_update;
#[cfg(any(feature = "mysql", feature = "mariadb"))]
mod insert_returning_id;
mod limit_offset;
mod query_fragment_impls;

/// The MySQL-Like query builder
#[allow(missing_debug_implementations)]
pub struct MysqlLikeQueryBuilder<DB: Backend> {
    sql: String,
    _phantom: PhantomData<DB>,
}

impl<DB: Backend> Default for MysqlLikeQueryBuilder<DB> {
    fn default() -> Self {
        Self {
            sql: String::default(),
            _phantom: PhantomData,
        }
    }
}

impl<DB: Backend> MysqlLikeQueryBuilder<DB> {
    /// Constructs a new query builder with an empty query
    pub fn new() -> Self {
        MysqlLikeQueryBuilder::default()
    }
}

impl<DB: Backend> QueryBuilder<DB> for MysqlLikeQueryBuilder<DB> {
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

    #[cfg(feature = "mysql_backend")]
    type TestBackend = crate::mysql::Mysql;
    #[cfg(all(not(feature = "mysql_backend"), feature = "mariadb_backend"))]
    type TestBackend = crate::mariadb::Mariadb;

    #[diesel_test_helper::test]
    fn push_identifier_escapes_embedded_backticks() {
        let mut builder = MysqlLikeQueryBuilder::<TestBackend>::new();
        builder.push_identifier("users").unwrap();
        builder.push_identifier("we`ird").unwrap();
        assert_eq!(builder.finish(), "`users``we``ird`");
    }
}
