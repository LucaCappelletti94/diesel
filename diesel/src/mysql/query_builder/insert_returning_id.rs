//! `execute_returning_id` for MySQL inserts.

use core::num::NonZeroU64;

use super::super::backend::Mysql;
use super::super::connection::MysqlConnection;
use crate::query_builder::{InsertStatement, QueryFragment, QueryId};
use crate::query_source::QuerySource;
use crate::result::QueryResult;

impl<T: QuerySource, U, Op, Ret> InsertStatement<T, U, Op, Ret> {
    /// Executes this insert and returns the `AUTO_INCREMENT` value it set, or
    /// `None` if it set none. The MySQL counterpart to `RETURNING`, without
    /// the extra round trip.
    ///
    /// See [the MySQL documentation](https://dev.mysql.com/doc/c-api/8.4/en/mysql-stmt-insert-id.html)
    /// for details.
    ///
    /// # Caveats
    /// - A key you supply is reported back rather than `None`, as is the key
    ///   of a row `ON DUPLICATE KEY UPDATE` updates
    /// - Inserting nothing also gives `None`: an empty `INSERT ... SELECT`, or
    ///   an `INSERT IGNORE` whose rows are all skipped
    /// - A multi-row insert reports its first value. The rest are consecutive
    ///   for a plain `INSERT`, but `INSERT ... SELECT` and partly explicit
    ///   keys may leave gaps
    /// - Differs from the SQL `LAST_INSERT_ID()` function in the cases above
    ///   and for `LAST_INSERT_ID(expr)`
    ///
    /// # Example
    /// ```rust
    /// # include!("../../doctest_setup.rs");
    /// # fn main() {
    /// #     run_test().unwrap();
    /// # }
    /// # fn run_test() -> QueryResult<()> {
    /// #     use schema::users::dsl::*;
    /// use core::num::NonZeroU64;
    /// let conn = &mut establish_connection();
    /// let new_id = diesel::insert_into(users)
    ///     .values(name.eq("Ruby"))
    ///     .execute_returning_id(conn)?;
    /// // Two users (ids 1 and 2) are seeded, so Ruby's generated id is 3.
    /// assert_eq!(new_id, NonZeroU64::new(3));
    /// # Ok(())
    /// # }
    /// ```
    pub fn execute_returning_id(self, conn: &mut MysqlConnection) -> QueryResult<Option<NonZeroU64>>
    where
        Self: QueryFragment<Mysql> + QueryId,
    {
        conn.execute_returning_id(&self)
    }
}
