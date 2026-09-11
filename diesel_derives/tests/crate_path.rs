//! Derive output has to resolve diesel independently of the caller's namespace.
//!
//! Both modules below shadow the name `diesel` with an empty module. The
//! `table!` invocation in each is the positive control: it already compiled
//! under that shadowing, so the absence of errors from the derives beside it
//! carries information.

use crate::helpers::TestBackend;
use diesel::prelude::*;

/// The only route `macro_generated` has to diesel. It is deliberately not
/// named `diesel`, so nothing in that module can reach the crate by its name.
pub mod deps {
    pub use ::diesel as orm;
}

/// A macro that reaches diesel only through `$crate`, the way a library that
/// exports schema macros has to.
macro_rules! self_contained_table {
    ($table:ident, $row:ident) => {
        $crate::crate_path::deps::orm::table! {
            $table (id) {
                id -> $crate::crate_path::deps::orm::sql_types::Integer,
                name -> $crate::crate_path::deps::orm::sql_types::Text,
            }
        }

        #[derive(
            $crate::crate_path::deps::orm::Insertable,
            $crate::crate_path::deps::orm::Queryable,
            $crate::crate_path::deps::orm::Selectable,
            $crate::crate_path::deps::orm::QueryableByName,
            $crate::crate_path::deps::orm::AsChangeset,
            $crate::crate_path::deps::orm::Identifiable,
        )]
        #[diesel(crate = $crate::crate_path::deps::orm, table_name = $table)]
        pub struct $row {
            pub id: i32,
            pub name: String,
        }
    };
}

mod shadowed {
    mod diesel {}

    ::diesel::table! {
        shadowed_users (id) {
            id -> ::diesel::sql_types::Integer,
            name -> ::diesel::sql_types::Text,
        }
    }

    ::diesel::table! {
        shadowed_posts (id) {
            id -> ::diesel::sql_types::Integer,
            user_id -> ::diesel::sql_types::Integer,
        }
    }

    #[derive(
        ::diesel::Insertable,
        ::diesel::Queryable,
        ::diesel::Selectable,
        ::diesel::QueryableByName,
        ::diesel::AsChangeset,
        ::diesel::Identifiable,
    )]
    #[diesel(table_name = shadowed_users)]
    pub struct User {
        pub id: i32,
        pub name: String,
    }

    #[derive(::diesel::HasQuery, ::diesel::Insertable)]
    #[diesel(table_name = shadowed_users)]
    pub struct UserQuery {
        pub id: i32,
        pub name: String,
    }

    #[derive(::diesel::Identifiable, ::diesel::Associations, ::diesel::Queryable)]
    #[diesel(table_name = shadowed_posts, belongs_to(User))]
    pub struct Post {
        pub id: i32,
        pub user_id: i32,
    }

    #[derive(Debug, ::diesel::AsExpression, ::diesel::FromSqlRow)]
    #[diesel(sql_type = ::diesel::sql_types::Text)]
    pub struct Name(pub String);

    #[derive(::diesel::SqlType)]
    pub struct MySqlType;

    #[derive(
        ::diesel::query_builder::QueryId,
        ::diesel::sql_types::DieselNumericOps,
        ::diesel::expression::ValidGrouping,
    )]
    pub struct Wrapper<T> {
        pub inner: T,
    }

    impl<T: ::diesel::expression::Expression> ::diesel::expression::Expression for Wrapper<T> {
        type SqlType = T::SqlType;
    }

    impl<T, DB> ::diesel::query_builder::QueryFragment<DB> for Wrapper<T>
    where
        DB: ::diesel::backend::Backend,
        T: ::diesel::query_builder::QueryFragment<DB>,
    {
        fn walk_ast<'b>(
            &'b self,
            pass: ::diesel::query_builder::AstPass<'_, 'b, DB>,
        ) -> ::diesel::QueryResult<()> {
            self.inner.walk_ast(pass)
        }
    }
}

mod macro_generated {
    mod diesel {}

    self_contained_table!(macro_users, MacroUser);
}

/// The `Insertable` of a struct whose module shadows `diesel` still builds a
/// statement for its table.
#[test]
fn a_derive_beside_a_shadowed_diesel_name_still_builds_its_query() {
    let row = shadowed::User {
        id: 1,
        name: "sean".into(),
    };
    let insert = diesel::insert_into(shadowed::shadowed_users::table).values(&row);

    let sql = diesel::debug_query::<TestBackend, _>(&insert).to_string();
    assert!(sql.contains("shadowed_users"), "{sql}");
}

/// The remaining derives produce items usable beside a shadowed `diesel`:
/// `SqlType` a type argument, `DieselNumericOps` an addition, `HasQuery` a base
/// query, `Associations` a child lookup.
#[test]
fn the_remaining_derives_beside_a_shadowed_diesel_name_are_usable() {
    fn assert_sql_type<T: diesel::sql_types::SqlType>() {}
    assert_sql_type::<shadowed::MySqlType>();

    let sum = shadowed::Wrapper {
        inner: shadowed::shadowed_users::id,
    } + 1;
    let sql = diesel::debug_query::<TestBackend, _>(&sum).to_string();
    assert!(sql.contains("id"), "{sql}");

    let insert = diesel::insert_into(shadowed::shadowed_users::table).values(shadowed::UserQuery {
        id: 3,
        name: "ada".into(),
    });
    let sql = diesel::debug_query::<TestBackend, _>(&insert).to_string();
    assert!(sql.contains("shadowed_users"), "{sql}");

    let base = <shadowed::UserQuery as diesel::HasQuery<TestBackend>>::base_query();
    let sql = diesel::debug_query::<TestBackend, _>(&base).to_string();
    assert!(sql.contains("shadowed_users"), "{sql}");

    let user = shadowed::User {
        id: 1,
        name: "sean".into(),
    };
    let posts = shadowed::Post::belonging_to(&user);
    let sql = diesel::debug_query::<TestBackend, _>(&posts).to_string();
    assert!(sql.contains("shadowed_posts"), "{sql}");
}

/// The same holds for a struct generated by a macro that never names diesel,
/// reaching it only through the `crate` attribute.
#[test]
fn a_macro_that_reaches_diesel_through_crate_generates_a_usable_row() {
    let row = macro_generated::MacroUser {
        id: 2,
        name: "tess".into(),
    };
    let insert = diesel::insert_into(macro_generated::macro_users::table).values(&row);

    let sql = diesel::debug_query::<TestBackend, _>(&insert).to_string();
    assert!(sql.contains("macro_users"), "{sql}");

    let select = macro_generated::macro_users::table
        .select(macro_generated::MacroUser::as_select())
        .filter(macro_generated::macro_users::id.eq(2));
    let sql = diesel::debug_query::<TestBackend, _>(&select).to_string();
    assert!(sql.contains("macro_users"), "{sql}");
}
