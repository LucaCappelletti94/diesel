use crate::query_builder::*;
use crate::query_source::Column;

/// Represents the column list for use in an insert statement.
///
/// This trait is implemented by columns and flat tuples of columns.
///
/// # Example
///
/// ```
/// use diesel::query_builder::ColumnList;
///
/// diesel::table! {
///     docs (tenant_id, id) {
///         tenant_id -> Integer,
///         id -> Integer,
///         title -> Text,
///     }
/// }
///
/// assert_eq!(<docs::id as ColumnList>::NAMES, &["id"]);
/// assert_eq!(
///     <(docs::tenant_id, docs::id) as ColumnList>::NAMES,
///     &["tenant_id", "id"],
/// );
/// ```
pub trait ColumnList {
    /// The table these columns belong to
    type Table;

    /// The unqualified column names in list order.
    const NAMES: &'static [&'static str];

    /// Generate the SQL for this column list.
    ///
    /// Column names must *not* be qualified.
    fn walk_ast<DB: Backend>(&self, out: AstPass<'_, '_, DB>) -> QueryResult<()>;
}

impl<C> ColumnList for C
where
    C: Column,
{
    type Table = <C as Column>::Table;

    const NAMES: &'static [&'static str] = &[C::NAME];

    fn walk_ast<DB: Backend>(&self, mut out: AstPass<'_, '_, DB>) -> QueryResult<()> {
        out.push_identifier(C::NAME)?;
        Ok(())
    }
}
