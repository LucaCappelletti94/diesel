use diesel::connection::{LoadConnection, SimpleConnection};
use diesel::prelude::*;
use diesel::result::Error;
use diesel::row::Row;
use diesel::sql_types::{Integer, Nullable, Text};
use diesel::sqlite::{SqliteBindValue, SqliteFunctionBehavior, register_dynamic_table_function};

diesel::table! {
    grants (id) {
        id -> Integer,
        role -> Text,
        name -> Text,
    }
}

diesel::table! {
    users (id) {
        id -> Integer,
        role -> Text,
        name -> Text,
    }
}

diesel::view! {
    grantees {
        name -> Text,
    }
}

diesel::view! {
    typed {
        number -> Integer,
        label -> Nullable<Text>,
        payload -> Binary,
        ratio -> Double,
    }
}

diesel::view! {
    countdown {
        value -> Integer,
    }
}

diesel::view! {
    single {
        value -> Text,
    }
}

diesel::view! {
    clashing {
        role -> Text,
    }
}

diesel::view! {
    case_clashing {
        #[sql_name = "ROLE"]
        output -> Text,
    }
}

diesel::view! {
    quoted {
        #[sql_name = "out`put \"value\""]
        output -> Text,
    }
}

diesel::view! {
    renamed {
        value -> Text,
    }
}

#[diesel::declare_sql_function]
extern "SQL" {
    #[query_source(grantees)]
    fn grantees(role: Text) -> grantees::SqlType;

    #[query_source(typed)]
    fn typed() -> typed::SqlType;

    #[query_source(countdown)]
    fn countdown(start: Integer) -> countdown::SqlType;

    #[query_source(single)]
    fn single() -> single::SqlType;

    #[query_source(clashing)]
    fn clashing(role: Text) -> clashing::SqlType;

    #[query_source(case_clashing)]
    fn case_clashing(role: Text) -> case_clashing::SqlType;

    #[query_source(quoted)]
    fn quoted(input: Text) -> quoted::SqlType;

    #[sql_name = "registered_name"]
    #[query_source(renamed)]
    fn rust_name() -> renamed::SqlType;

    #[query_source(single)]
    #[expect(non_snake_case, reason = "Exercises generated generic-name hygiene")]
    fn shadowing_arguments(
        connection: Text,
        function: Text,
        F: Text,
        Rows: Text,
        behavior: Text,
    ) -> single::SqlType;
}

diesel::allow_tables_to_appear_in_same_query!(grants, grantees);
diesel::allow_tables_to_appear_in_same_query!(users, grantees);

fn connection() -> SqliteConnection {
    let mut connection = SqliteConnection::establish(":memory:").unwrap();
    connection
        .batch_execute(
            "CREATE TABLE grants (id INTEGER PRIMARY KEY, role TEXT NOT NULL, name TEXT NOT NULL);
             INSERT INTO grants (role, name) VALUES ('admin', 'alice'), ('admin', 'bob'), ('guest', 'carol');",
        )
        .unwrap();
    connection
}

fn register_grantees(connection: &mut SqliteConnection, behavior: SqliteFunctionBehavior) {
    grantees_utils::register_impl_with_behavior(
        connection,
        behavior,
        |connection, role: String| {
            grants::table
                .filter(grants::role.eq(role))
                .select((grants::name,))
                .order(grants::name)
                .load::<(String,)>(connection)
        },
    )
    .unwrap();
}

fn register_single<Function>(
    connection: &mut SqliteConnection,
    behavior: SqliteFunctionBehavior,
    rows: Function,
) where
    Function: Fn() -> QueryResult<Vec<(String,)>> + Send + core::panic::UnwindSafe + 'static,
{
    single_utils::register_impl_with_behavior(connection, behavior, move |_| rows()).unwrap();
}

fn texts(connection: &mut SqliteConnection, query: &str) -> QueryResult<Vec<String>> {
    let mut texts = Vec::new();
    // Raw SQL exercises SQLite's module interface independently of the generated call.
    for row in connection.load(diesel::sql_query(query))? {
        texts.push(
            row?.get_value::<Text, String, _>(0)
                .map_err(Error::DeserializationError)?,
        );
    }
    Ok(texts)
}

#[diesel_test_helper::test]
fn column_names_with_quote_characters_are_declared_verbatim() {
    let connection = &mut connection();
    quoted_utils::register_impl(connection, |_, input: String| {
        Ok(vec![(format!("{input}!"),)])
    })
    .unwrap();
    let output = quoted("echo")
        .select(quoted::output)
        .load::<String>(connection);
    assert_eq!(output.unwrap(), ["echo!"]);

    register_dynamic_table_function(
        connection,
        "quoted_parameters",
        &["out`put \"value\""],
        &["in`put"],
        SqliteFunctionBehavior::empty(),
        |_, arguments| {
            let input = arguments
                .get_value::<Text, String, _>(0)
                .map_err(Error::DeserializationError)?;
            Ok([[SqliteBindValue::from(input)]])
        },
    )
    .unwrap();
    assert_eq!(
        texts(
            connection,
            "SELECT CAST(\"out`put \"\"value\"\"\" AS TEXT) FROM quoted_parameters('echo')"
        )
        .unwrap(),
        ["echo"]
    );
}

#[diesel_test_helper::test]
fn the_query_dsl_calls_the_function() {
    let connection = &mut connection();
    register_grantees(connection, SqliteFunctionBehavior::empty());
    let admins = grantees("admin")
        .select(grantees::name)
        .order(grantees::name)
        .load::<String>(connection);
    assert_eq!(admins.unwrap(), ["alice", "bob"]);
    let rows = grantees("guest").load::<(String,)>(connection);
    assert_eq!(rows.unwrap(), [("carol".to_string(),)]);
    assert_eq!(
        texts(connection, "SELECT name FROM grantees('admin')").unwrap(),
        ["alice", "bob"]
    );
}

#[diesel_test_helper::test]
fn a_correlated_inner_join_returns_each_roles_grantees() {
    let connection = &mut connection();
    register_grantees(connection, SqliteFunctionBehavior::empty());
    let pairs = connection
        .load(diesel::sql_query(
            "SELECT g.name, x.name FROM grants g JOIN grantees(g.role) x ORDER BY g.name, x.name",
        ))
        .unwrap()
        .map(|row| {
            let row = row.unwrap();
            (
                row.get_value::<Text, String, _>(0).unwrap(),
                row.get_value::<Text, String, _>(1).unwrap(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        pairs,
        [
            ("alice".to_string(), "alice".to_string()),
            ("alice".to_string(), "bob".to_string()),
            ("bob".to_string(), "alice".to_string()),
            ("bob".to_string(), "bob".to_string()),
            ("carol".to_string(), "carol".to_string()),
        ]
    );
}

#[diesel_test_helper::test]
fn a_correlated_left_join_preserves_grantees_without_peers() {
    let connection = &mut connection();
    register_grantees(connection, SqliteFunctionBehavior::empty());
    let pairs = connection
        .load(diesel::sql_query(
            "SELECT g.name, x.name FROM grants g LEFT JOIN grantees(g.role) x ON x.name <> g.name ORDER BY g.name, x.name",
        ))
        .unwrap()
        .map(|row| {
            let row = row.unwrap();
            (
                row.get_value::<Text, String, _>(0).unwrap(),
                row.get_value::<Nullable<Text>, Option<String>, _>(1)
                    .unwrap(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        pairs,
        [
            ("alice".to_string(), Some("bob".to_string())),
            ("bob".to_string(), Some("alice".to_string())),
            ("carol".to_string(), None),
        ]
    );
}

#[diesel_test_helper::test]
fn registered_table_function_inner_join_lateral_reads_user_arguments() {
    let connection = &mut connection();
    register_grantees(connection, SqliteFunctionBehavior::empty());
    connection
        .batch_execute(
            "CREATE TABLE users (id INTEGER PRIMARY KEY, role TEXT NOT NULL, name TEXT NOT NULL);
             INSERT INTO users (role, name) VALUES ('admin', 'alice'), ('guest', 'carol'), ('missing', 'dave');",
        )
        .unwrap();
    let pairs = users::table
        .inner_join_lateral(grantees(users::role).on(grantees::name.ne(users::name)))
        .select((users::name, grantees::name))
        .order((users::name, grantees::name))
        .load::<(String, String)>(connection)
        .unwrap();
    assert_eq!(pairs, [("alice".to_string(), "bob".to_string())]);
}

#[diesel_test_helper::test]
fn registered_table_function_left_join_lateral_preserves_empty_results() {
    let connection = &mut connection();
    register_grantees(connection, SqliteFunctionBehavior::empty());
    connection
        .batch_execute(
            "CREATE TABLE users (id INTEGER PRIMARY KEY, role TEXT NOT NULL, name TEXT NOT NULL);
             INSERT INTO users (role, name) VALUES ('admin', 'alice'), ('guest', 'carol'), ('missing', 'dave');",
        )
        .unwrap();
    let pairs = users::table
        .left_join_lateral(grantees(users::role).on(grantees::name.ne(users::name)))
        .select((users::name, grantees::name.nullable()))
        .order((users::name, grantees::name))
        .load::<(String, Option<String>)>(connection)
        .unwrap();
    assert_eq!(
        pairs,
        [
            ("alice".to_string(), Some("bob".to_string())),
            ("carol".to_string(), None),
            ("dave".to_string(), None),
        ]
    );
}

#[diesel_test_helper::test]
fn a_call_requires_its_declared_argument() {
    let connection = &mut connection();
    register_grantees(connection, SqliteFunctionBehavior::empty());
    let error = texts(connection, "SELECT name FROM grantees()").unwrap_err();
    assert!(error.to_string().contains("no query solution"), "{error}");
}

#[diesel_test_helper::test]
fn a_dynamic_call_requires_its_declared_argument() {
    let connection = &mut connection();
    register_dynamic_table_function(
        connection,
        "dynamic_grantees",
        &["name"],
        &["role"],
        SqliteFunctionBehavior::empty(),
        |_, _| Ok(vec![vec![SqliteBindValue::from("alice".to_string())]]),
    )
    .unwrap();
    assert_eq!(
        texts(connection, "SELECT name FROM dynamic_grantees('admin')").unwrap(),
        ["alice"]
    );
    let error = texts(connection, "SELECT name FROM dynamic_grantees()").unwrap_err();
    assert!(error.to_string().contains("no query solution"), "{error}");
}

#[diesel_test_helper::test]
fn declared_parameters_do_not_shadow_registration_helpers() {
    let connection = &mut connection();
    let implementation = |connection: &mut diesel::sqlite::BorrowedSqliteConnection,
                          connection_argument: String,
                          function_argument: String,
                          callback_argument: String,
                          rows_argument: String,
                          behavior_argument: String| {
        assert_eq!(grants::table.count().get_result::<i64>(connection)?, 3);
        Ok(vec![(format!(
            "{connection_argument} {function_argument} {callback_argument} {rows_argument} {behavior_argument}"
        ),)])
    };
    shadowing_arguments_utils::register_impl(connection, implementation).unwrap();
    assert_eq!(
        texts(
            connection,
            "SELECT value FROM shadowing_arguments('a', 'b', 'c', 'd', 'e')"
        )
        .unwrap(),
        ["a b c d e"]
    );
    shadowing_arguments_utils::register_impl_with_behavior(
        connection,
        SqliteFunctionBehavior::empty(),
        implementation,
    )
    .unwrap();
    assert_eq!(
        texts(
            connection,
            "SELECT value FROM shadowing_arguments('v', 'w', 'x', 'y', 'z')"
        )
        .unwrap(),
        ["v w x y z"]
    );
}

#[diesel_test_helper::test]
fn registration_uses_the_sql_name() {
    let connection = &mut connection();
    rust_name_utils::register_impl(connection, |_| Ok(vec![("registered",)])).unwrap();
    assert_eq!(
        rust_name()
            .select(renamed::value)
            .load::<String>(connection)
            .unwrap(),
        ["registered"]
    );
    assert_eq!(
        texts(connection, "SELECT value FROM registered_name()").unwrap(),
        ["registered"]
    );
    assert!(texts(connection, "SELECT value FROM rust_name()").is_err());
}

#[diesel_test_helper::test]
fn registering_a_name_again_replaces_the_function_in_cached_statements() {
    let connection = &mut connection();
    register_single(connection, SqliteFunctionBehavior::empty(), || {
        Ok(vec![("first".to_string(),)])
    });
    let load = |connection: &mut SqliteConnection| {
        single()
            .select(single::value)
            .load::<String>(connection)
            .unwrap()
    };
    assert_eq!(load(connection), ["first"]);
    register_single(connection, SqliteFunctionBehavior::empty(), || {
        Ok(vec![("second".to_string(),)])
    });
    assert_eq!(load(connection), ["second"]);
}

#[diesel_test_helper::test]
fn an_uncorrelated_call_is_an_eq_any_subselect() {
    let connection = &mut connection();
    register_grantees(connection, SqliteFunctionBehavior::empty());
    let admins = grants::table
        .filter(grants::name.eq_any(grantees("admin").select(grantees::name)))
        .select(grants::id)
        .order(grants::id)
        .load::<i32>(connection);
    assert_eq!(admins.unwrap(), [1, 2]);
}

#[diesel_test_helper::test]
fn values_keep_their_sql_types() {
    let connection = &mut connection();
    typed_utils::register_impl(connection, |_| {
        Ok(vec![
            (7, Some("seven"), vec![0_u8, 1, 2], 1.5),
            (0, None, Vec::new(), -0.5),
        ])
    })
    .unwrap();
    let rows = typed().load::<(i32, Option<String>, Vec<u8>, f64)>(connection);
    assert_eq!(
        rows.unwrap(),
        [
            (7, Some("seven".to_string()), vec![0, 1, 2], 1.5),
            (0, None, Vec::new(), -0.5),
        ]
    );
    assert_eq!(
        texts(
            connection,
            "SELECT typeof(number) || ' ' || typeof(label) || ' ' || typeof(payload) || ' ' || typeof(ratio) FROM typed"
        )
        .unwrap(),
        ["integer text blob real", "integer null blob real"]
    );
}

#[diesel_test_helper::test]
fn errors_fail_the_statement() {
    let connection = &mut connection();
    register_single(connection, SqliteFunctionBehavior::empty(), || {
        Err(Error::QueryBuilderError("no rows today".into()))
    });
    let error = single().load::<(String,)>(connection).unwrap_err();
    assert!(error.to_string().contains("no rows today"), "{error}");
}

#[cfg(not(all(target_family = "wasm", target_os = "unknown")))]
#[diesel_test_helper::test]
fn a_panic_fails_the_statement() {
    let connection = &mut connection();
    register_single(connection, SqliteFunctionBehavior::empty(), || {
        panic!("boom")
    });
    let error = single().load::<(String,)>(connection).unwrap_err();
    assert!(error.to_string().contains("`single` panicked"), "{error}");
    let name = grants::table
        .find(1)
        .select(grants::name)
        .first::<String>(connection);
    assert_eq!(name, Ok("alice".to_string()));
}

#[diesel_test_helper::test]
fn registration_rejects_deterministic_behavior() {
    let connection = &mut connection();
    let error = grantees_utils::register_impl_with_behavior(
        connection,
        SqliteFunctionBehavior::DETERMINISTIC,
        |_, _: String| Ok(Vec::<(String,)>::new()),
    )
    .unwrap_err();
    assert!(error.to_string().contains("DETERMINISTIC"), "{error}");
}

#[diesel_test_helper::test]
fn a_parameter_cannot_share_a_result_column_name() {
    let connection = &mut connection();
    let error =
        clashing_utils::register_impl(connection, |_, _: String| Ok(Vec::<(String,)>::new()))
            .unwrap_err();
    assert!(
        error.to_string().to_ascii_lowercase().contains("role"),
        "{error}"
    );
}

#[diesel_test_helper::test]
fn parameter_and_column_names_collide_case_insensitively() {
    let connection = &mut connection();
    let error =
        case_clashing_utils::register_impl(connection, |_, _: String| Ok(Vec::<(String,)>::new()))
            .unwrap_err();
    assert!(
        error.to_string().to_ascii_lowercase().contains("role"),
        "{error}"
    );
}

#[diesel_test_helper::test]
fn behavior_controls_use_from_views_with_an_untrusted_schema() {
    let connection = &mut connection();
    connection.set_trusted_schema(false).unwrap();
    register_grantees(connection, SqliteFunctionBehavior::INNOCUOUS);
    register_single(connection, SqliteFunctionBehavior::empty(), || {
        Ok(vec![("hidden".to_string(),)])
    });
    connection
        .batch_execute(
            "CREATE VIEW admins AS SELECT name FROM grantees('admin');
         CREATE VIEW untrusted_view AS SELECT value FROM single;",
        )
        .unwrap();
    assert_eq!(
        texts(connection, "SELECT name FROM admins").unwrap(),
        ["alice", "bob"]
    );
    let error = texts(connection, "SELECT value FROM untrusted_view").unwrap_err();
    assert!(
        error.to_string().contains("unsafe use of virtual table"),
        "{error}"
    );
}

#[diesel_test_helper::test]
fn default_behavior_is_neither_innocuous_nor_directonly() {
    let connection = &mut connection();
    single_utils::register_impl(connection, |_| Ok(vec![("visible",)])).unwrap();
    connection.set_trusted_schema(true).unwrap();
    connection
        .batch_execute("CREATE VIEW default_view AS SELECT value FROM single")
        .unwrap();
    assert_eq!(
        texts(connection, "SELECT value FROM default_view").unwrap(),
        ["visible"]
    );
    connection.set_trusted_schema(false).unwrap();
    let error = texts(connection, "SELECT value FROM default_view").unwrap_err();
    assert!(
        error.to_string().contains("unsafe use of virtual table"),
        "{error}"
    );
    assert_eq!(
        single()
            .select(single::value)
            .load::<String>(connection)
            .unwrap(),
        ["visible"]
    );
}

#[diesel_test_helper::test]
fn directonly_refuses_use_from_views() {
    let connection = &mut connection();
    connection.set_trusted_schema(true).unwrap();
    register_grantees(connection, SqliteFunctionBehavior::DIRECTONLY);
    connection
        .batch_execute("CREATE VIEW admins AS SELECT name FROM grantees('admin');")
        .unwrap();
    assert_eq!(
        texts(connection, "SELECT name FROM grantees('admin')").unwrap(),
        ["alice", "bob"]
    );
    let error = texts(connection, "SELECT name FROM admins").unwrap_err();
    assert!(
        error.to_string().contains("unsafe use of virtual table"),
        "{error}"
    );
}

#[diesel_test_helper::test]
fn a_trigger_program_reads_what_it_wrote_through_the_function() {
    let connection = &mut connection();
    register_grantees(connection, SqliteFunctionBehavior::INNOCUOUS);
    connection
        .batch_execute(
            "CREATE TABLE requests (role TEXT NOT NULL, name TEXT NOT NULL);
         CREATE TABLE audit (name TEXT NOT NULL);
         CREATE TRIGGER grant_request AFTER INSERT ON requests BEGIN
             INSERT INTO grants (role, name) VALUES (NEW.role, NEW.name);
             INSERT INTO audit (name) SELECT name FROM grantees(NEW.role);
             INSERT INTO grants (role, name) SELECT NEW.role, name || '+' FROM grantees(NEW.role);
         END;
         INSERT INTO requests (role, name) VALUES ('guest', 'dave');",
        )
        .unwrap();
    assert_eq!(
        texts(connection, "SELECT name FROM audit ORDER BY name").unwrap(),
        ["carol", "dave"]
    );
    let guests = grantees("guest")
        .select(grantees::name)
        .order(grantees::name)
        .load::<String>(connection);
    assert_eq!(guests.unwrap(), ["carol", "carol+", "dave", "dave+"]);
}

#[diesel_test_helper::test]
fn a_function_may_call_itself() {
    let connection = &mut connection();
    countdown_utils::register_impl(connection, |connection, start: i32| {
        let mut rows = vec![(start,)];
        if start > 0 {
            rows.extend(
                countdown(start - 1)
                    .select((countdown::value,))
                    .load::<(i32,)>(connection)?,
            );
        }
        Ok(rows)
    })
    .unwrap();
    let values = countdown(3)
        .select(countdown::value)
        .load::<i32>(connection);
    assert_eq!(values.unwrap(), [3, 2, 1, 0]);
}

#[diesel_test_helper::test]
fn a_declaration_named_at_run_time_is_checked_row_by_row() {
    let connection = &mut connection();
    let register = |connection: &mut SqliteConnection, rows: Vec<Vec<i64>>| {
        register_dynamic_table_function(
            connection,
            "runtime",
            &["first", "second"],
            &[],
            SqliteFunctionBehavior::empty(),
            move |_, _| {
                Ok(rows
                    .clone()
                    .into_iter()
                    .map(|row| row.into_iter().map(SqliteBindValue::from)))
            },
        )
        .unwrap();
    };
    register(connection, vec![vec![1, 2]]);
    assert_eq!(
        texts(connection, "SELECT first || ',' || second FROM runtime").unwrap(),
        ["1,2"]
    );
    for invalid_row in [vec![1], vec![1, 2, 3]] {
        let width = invalid_row.len();
        register(connection, vec![vec![1, 2], invalid_row]);
        let error = texts(connection, "SELECT first FROM runtime").unwrap_err();
        assert!(
            error
                .to_string()
                .contains(&format!("has {width} values for 2 columns")),
            "{error}"
        );
    }
}
