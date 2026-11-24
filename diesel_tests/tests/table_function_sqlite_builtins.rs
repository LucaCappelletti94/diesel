#![cfg(all(feature = "sqlite", not(miri)))]

use crate::schema::*;
use diesel::connection::SimpleConnection;
use diesel::prelude::*;
use diesel::sql_types::{Binary, Text};
use diesel::sqlite::table_functions::*;

diesel::view! {
    json_numbers {
        key -> Integer,
        value -> Integer,
    }
}

diesel::view! {
    json_strings {
        value -> Text,
    }
}

diesel::view! {
    json_atoms {
        atom -> Nullable<Integer>,
    }
}

diesel::view! {
    json_containers {
        value -> Binary,
    }
}

diesel::allow_tables_to_appear_in_same_query!(users; pragma_table_info, json_strings);
diesel::allow_tables_to_appear_in_same_query!(json_strings, pragma_table_info);

#[diesel_test_helper::test]
fn pragma_table_and_index_functions_load_all_arities() {
    let connection = &mut connection();
    connection.batch_execute("CREATE TABLE builtin_sample (identifier INTEGER PRIMARY KEY, label TEXT DEFAULT 'hello'); CREATE INDEX builtin_label ON builtin_sample(label);").unwrap();

    macro_rules! names {
        ($function:expr, $column:expr, $expected:expr) => {
            assert_eq!(
                $function
                    .select($column)
                    .load::<String>(connection)
                    .unwrap(),
                $expected
            );
        };
    }
    let columns = vec!["identifier".to_owned(), "label".to_owned()];
    names!(
        pragma_table_info("builtin_sample"),
        pragma_table_info::name,
        columns
    );
    names!(
        pragma_table_info_with_schema("builtin_sample", "main"),
        pragma_table_info::name,
        columns
    );
    names!(
        pragma_table_xinfo("builtin_sample"),
        pragma_table_xinfo::name,
        columns
    );
    names!(
        pragma_table_xinfo_with_schema("builtin_sample", "main"),
        pragma_table_xinfo::name,
        columns
    );
    names!(
        pragma_table_list().filter(pragma_table_list::name.eq("builtin_sample")),
        pragma_table_list::name,
        vec!["builtin_sample"]
    );
    names!(
        pragma_table_list_for_table("builtin_sample"),
        pragma_table_list::name,
        vec!["builtin_sample"]
    );
    names!(
        pragma_index_list("builtin_sample"),
        pragma_index_list::name,
        vec!["builtin_label"]
    );
    names!(
        pragma_index_list_with_schema("builtin_sample", "main"),
        pragma_index_list::name,
        vec!["builtin_label"]
    );
    assert_eq!(
        pragma_index_info("builtin_label")
            .load::<(i32, i32, Option<String>)>(connection)
            .unwrap(),
        vec![(0, 1, Some("label".to_owned()))]
    );
    assert_eq!(
        pragma_index_info_with_schema("builtin_label", "main")
            .select(pragma_index_info::name)
            .load::<Option<String>>(connection)
            .unwrap(),
        vec![Some("label".to_owned())]
    );
    let index_columns = vec![Some("label".to_owned()), None];
    assert_eq!(
        pragma_index_xinfo("builtin_label")
            .select(pragma_index_xinfo::name)
            .load::<Option<String>>(connection)
            .unwrap(),
        index_columns
    );
    assert_eq!(
        pragma_index_xinfo_with_schema("builtin_label", "main")
            .select(pragma_index_xinfo::name)
            .load::<Option<String>>(connection)
            .unwrap(),
        index_columns
    );
    assert_eq!(
        pragma_table_info("builtin_sample")
            .select(pragma_table_info::dflt_value)
            .load::<Option<String>>(connection)
            .unwrap(),
        vec![None, Some("'hello'".to_owned())]
    );
}

#[diesel_test_helper::test]
fn foreign_key_functions_load_all_arities_and_nullable_columns() {
    let connection = &mut connection();
    disable_foreign_keys(connection);
    connection.batch_execute("CREATE TABLE builtin_parent (identifier INTEGER PRIMARY KEY); CREATE TABLE builtin_child (identifier INTEGER PRIMARY KEY, parent INTEGER REFERENCES builtin_parent); INSERT INTO builtin_child VALUES (1, 42);").unwrap();
    assert_eq!(
        pragma_foreign_key_list("builtin_child")
            .select(pragma_foreign_key_list::to_column)
            .load::<Option<String>>(connection)
            .unwrap(),
        vec![None]
    );
    assert_eq!(
        pragma_foreign_key_list_with_schema("builtin_child", "main")
            .select(pragma_foreign_key_list::from_column)
            .load::<String>(connection)
            .unwrap(),
        vec!["parent"]
    );
    macro_rules! violation {
        ($function:expr) => {
            assert_eq!(
                $function
                    .select((
                        pragma_foreign_key_check::table_name,
                        pragma_foreign_key_check::rowid,
                        pragma_foreign_key_check::parent,
                        pragma_foreign_key_check::fkid
                    ))
                    .load::<(String, Option<i64>, String, i32)>(connection)
                    .unwrap(),
                vec![(
                    "builtin_child".to_owned(),
                    Some(1),
                    "builtin_parent".to_owned(),
                    0
                )]
            );
        };
    }
    violation!(pragma_foreign_key_check());
    violation!(pragma_foreign_key_check_for_table("builtin_child"));
    violation!(pragma_foreign_key_check_with_schema(
        Some("builtin_child"),
        "main"
    ));
    violation!(pragma_foreign_key_check_with_schema(None::<&str>, "main"));
}

#[diesel_test_helper::test]
fn connection_and_integrity_pragmas_load_all_arities() {
    let connection = &mut connection();
    assert!(
        pragma_database_list()
            .select(pragma_database_list::name)
            .load::<String>(connection)
            .unwrap()
            .contains(&"main".to_owned())
    );
    assert!(
        pragma_collation_list()
            .select(pragma_collation_list::name)
            .load::<String>(connection)
            .unwrap()
            .contains(&"BINARY".to_owned())
    );
    assert!(
        pragma_function_list()
            .select(pragma_function_list::name)
            .load::<String>(connection)
            .unwrap()
            .contains(&"abs".to_owned())
    );
    assert!(
        pragma_module_list()
            .select(pragma_module_list::name)
            .load::<String>(connection)
            .unwrap()
            .contains(&"pragma_module_list".to_owned())
    );
    assert!(
        pragma_pragma_list()
            .select(pragma_pragma_list::name)
            .load::<String>(connection)
            .unwrap()
            .contains(&"table_info".to_owned())
    );
    assert!(
        !pragma_compile_options()
            .load::<(String,)>(connection)
            .unwrap()
            .is_empty()
    );
    macro_rules! healthy {
        ($function:expr) => {
            assert_eq!(
                $function.load::<(String,)>(connection).unwrap(),
                vec![("ok".to_owned(),)]
            );
        };
    }
    healthy!(pragma_integrity_check());
    healthy!(pragma_integrity_check_for_table("users"));
    healthy!(pragma_integrity_check_with_schema(Some("users"), "main"));
    healthy!(pragma_integrity_check_with_schema(None::<&str>, "main"));
    healthy!(pragma_quick_check());
    healthy!(pragma_quick_check_for_table("users"));
    healthy!(pragma_quick_check_with_schema(Some("users"), "main"));
    healthy!(pragma_quick_check_with_schema(None::<&str>, "main"));
}

#[diesel_test_helper::test]
fn json_functions_keep_integer_storage_and_accept_paths() {
    let connection = &mut connection();
    let document = "[1,2]";
    let nested = "{\"numbers\":[1,2]}";
    macro_rules! numbers {
        ($function:expr) => {
            assert_eq!(
                $function
                    .order(json_numbers::key)
                    .load::<(i32, i32)>(connection)
                    .unwrap(),
                vec![(0, 1), (1, 2)]
            );
        };
    }
    numbers!(json_each::<json_numbers::view, Text, _>(document));
    numbers!(json_each_with_path::<json_numbers::view, Text, _, _>(
        nested,
        "$.numbers"
    ));
    macro_rules! atoms {
        ($function:expr) => {
            assert_eq!(
                $function
                    .filter(json_atoms::atom.is_not_null())
                    .select(json_atoms::atom)
                    .load::<Option<i32>>(connection)
                    .unwrap(),
                vec![Some(1), Some(2)]
            );
        };
    }
    atoms!(json_tree::<json_atoms::view, Text, _>(document));
    atoms!(json_tree_with_path::<json_atoms::view, Text, _, _>(
        nested,
        "$.numbers"
    ));
    assert_eq!(
        json_each::<json_numbers::view, Text, _>(document)
            .filter(json_numbers::value.eq(1))
            .select(json_numbers::value)
            .load::<i32>(connection)
            .unwrap(),
        vec![1]
    );
}

#[diesel_test_helper::test]
fn jsonb_functions_keep_integer_storage_and_accept_paths() {
    let connection = &mut connection();
    let version = diesel::select(diesel::dsl::sql::<Text>("sqlite_version()"))
        .get_result::<String>(connection)
        .unwrap();
    let version = version
        .split('.')
        .map(|component| component.parse::<u32>().unwrap())
        .collect::<Vec<_>>();
    if version.as_slice() < [3, 51, 0].as_slice() {
        return;
    }
    let document = "[1,2]";
    let nested = "{\"numbers\":[1,2]}";
    macro_rules! numbers {
        ($function:expr) => {
            assert_eq!(
                $function
                    .order(json_numbers::key)
                    .load::<(i32, i32)>(connection)
                    .unwrap(),
                vec![(0, 1), (1, 2)]
            );
        };
    }
    macro_rules! atoms {
        ($function:expr) => {
            assert_eq!(
                $function
                    .filter(json_atoms::atom.is_not_null())
                    .select(json_atoms::atom)
                    .load::<Option<i32>>(connection)
                    .unwrap(),
                vec![Some(1), Some(2)]
            );
        };
    }
    numbers!(jsonb_each::<json_numbers::view, Text, _>(document));
    numbers!(jsonb_each_with_path::<json_numbers::view, Text, _, _>(
        nested,
        "$.numbers"
    ));
    let binary = diesel::select(diesel::dsl::sql::<Binary>("jsonb('[1,2]')"))
        .get_result::<Vec<u8>>(connection)
        .unwrap();
    numbers!(jsonb_each::<json_numbers::view, Binary, _>(&binary));
    numbers!(jsonb_each_with_path::<json_numbers::view, Binary, _, _>(
        &binary, "$"
    ));
    atoms!(jsonb_tree::<json_atoms::view, Text, _>(document));
    atoms!(jsonb_tree_with_path::<json_atoms::view, Text, _, _>(
        nested,
        "$.numbers"
    ));
    atoms!(jsonb_tree::<json_atoms::view, Binary, _>(&binary));
    atoms!(jsonb_tree_with_path::<json_atoms::view, Binary, _, _>(
        &binary, "$"
    ));
    assert_eq!(
        jsonb_each::<json_containers::view, Text, _>("[[1,2]]")
            .select(json_containers::value)
            .get_result::<Vec<u8>>(connection)
            .unwrap(),
        binary
    );
}

#[diesel_test_helper::test]
fn builtin_relations_join_user_tables_through_semicolon_pairs() {
    let connection = &mut connection_with_sean_and_tess_in_users_table();
    let names = users::table
        .inner_join(
            json_each::<json_strings::view, Text, _>(r#"["Sean"]"#)
                .on(json_strings::value.eq(users::name)),
        )
        .select(users::name)
        .load::<String>(connection)
        .unwrap();
    assert_eq!(names, vec!["Sean"]);
    let names = users::table
        .inner_join(pragma_table_info("users").on(pragma_table_info::name.eq("name")))
        .select(users::name)
        .order(users::name)
        .load::<String>(connection)
        .unwrap();
    assert_eq!(names, vec!["Sean", "Tess"]);
}

#[diesel_test_helper::test]
fn two_builtin_relations_join_a_user_table() {
    let connection = &mut connection_with_sean_and_tess_in_users_table();
    let names = users::table
        .inner_join(pragma_table_info("users").on(pragma_table_info::name.eq("name")))
        .inner_join(
            json_each::<json_strings::view, Text, _>(r#"["Sean"]"#)
                .on(json_strings::value.eq(users::name)),
        )
        .select(users::name)
        .load::<String>(connection)
        .unwrap();
    assert_eq!(names, vec!["Sean"]);
}

#[diesel_test_helper::test]
fn json_functions_accept_nullable_documents() {
    use diesel::sql_types::Nullable;

    let connection = &mut connection();
    macro_rules! empty {
        ($function:expr) => {
            assert_eq!($function.count().get_result::<i64>(connection).unwrap(), 0);
        };
    }
    empty!(json_each::<json_numbers::view, Nullable<Text>, _>(
        None::<&str>
    ));
    empty!(json_each_with_path::<
        json_numbers::view,
        Nullable<Text>,
        _,
        _,
    >(None::<&str>, "$"));
    empty!(json_tree::<json_atoms::view, Nullable<Text>, _>(
        None::<&str>
    ));
    empty!(json_tree_with_path::<json_atoms::view, Nullable<Text>, _, _>(None::<&str>, "$"));
    assert_eq!(
        json_each::<json_numbers::view, Nullable<Text>, _>(Some("[1,2]"))
            .select(json_numbers::value)
            .load::<i32>(connection)
            .unwrap(),
        vec![1, 2]
    );
    let version = diesel::select(diesel::dsl::sql::<Text>("sqlite_version()"))
        .get_result::<String>(connection)
        .unwrap();
    let version = version
        .split('.')
        .map(|component| component.parse::<u32>().unwrap())
        .collect::<Vec<_>>();
    if version.as_slice() < [3, 51, 0].as_slice() {
        return;
    }
    empty!(jsonb_each::<json_numbers::view, Nullable<Text>, _>(
        None::<&str>
    ));
    empty!(jsonb_each_with_path::<
        json_numbers::view,
        Nullable<Text>,
        _,
        _,
    >(None::<&str>, "$"));
    empty!(jsonb_tree::<json_atoms::view, Nullable<Binary>, _>(
        None::<&[u8]>
    ));
    empty!(jsonb_tree_with_path::<
        json_atoms::view,
        Nullable<Binary>,
        _,
        _,
    >(None::<&[u8]>, "$"));
}

#[diesel_test_helper::test]
fn return_type_helpers_name_builtin_calls() {
    use diesel::expression::SqlLiteral;
    use diesel::sql_types::Nullable;

    let connection = &mut connection();
    let tables: helper_types::pragma_table_info<SqlLiteral<Text>> =
        pragma_table_info(diesel::dsl::sql::<Text>("'users'"));
    assert!(tables.count().get_result::<i64>(connection).unwrap() > 0);

    let elements: helper_types::json_each<json_strings::view, SqlLiteral<Nullable<Text>>> =
        json_each(diesel::dsl::sql::<Nullable<Text>>(r#"'["hello"]'"#));
    assert_eq!(
        elements
            .select(json_strings::value)
            .load::<String>(connection)
            .unwrap(),
        ["hello"]
    );
}
