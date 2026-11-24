use crate::schema::*;
use diesel::dsl::sql;
use diesel::pg::data_types::{PgInterval, PgNumeric, PgTimestamp};
use diesel::pg::table_functions::*;
use diesel::prelude::*;
use diesel::sql_types::*;

diesel::view! { integer_series { value -> Integer, } }
diesel::view! { bigint_series { value -> BigInt, } }
diesel::view! { numeric_series { value -> Numeric, } }
diesel::view! { timestamp_series { value -> Timestamp, } }
diesel::view! { timestamptz_series { value -> Timestamptz, } }
diesel::view! { array_elements { value -> Nullable<Integer>, } }

diesel::allow_tables_to_appear_in_same_query!(users; json_each_text, jsonb_each_text);

#[diesel_test_helper::test]
fn json_object_functions_load_rows() {
    let connection = &mut connection();
    assert_eq!(
        json_each(sql::<Json>("'{\"a\":1}'::json"))
            .load::<(String, serde_json::Value)>(connection)
            .unwrap(),
        [("a".into(), serde_json::json!(1))]
    );
    assert_eq!(
        jsonb_each(sql::<Jsonb>("'{\"a\":1}'::jsonb"))
            .load::<(String, serde_json::Value)>(connection)
            .unwrap(),
        [("a".into(), serde_json::json!(1))]
    );
    assert_eq!(
        json_each_text(sql::<Json>("'{\"a\":null,\"b\":1}'::json"))
            .order(json_each_text::key)
            .load::<(String, Option<String>)>(connection)
            .unwrap(),
        [("a".into(), None), ("b".into(), Some("1".into()))]
    );
    assert_eq!(
        jsonb_each_text(sql::<Jsonb>("'{\"a\":null,\"b\":1}'::jsonb"))
            .order(jsonb_each_text::key)
            .load::<(String, Option<String>)>(connection)
            .unwrap(),
        [("a".into(), None), ("b".into(), Some("1".into()))]
    );
    assert_eq!(
        json_object_keys(sql::<Json>("'{\"a\":1}'::json"))
            .select(json_object_keys::value)
            .load::<String>(connection)
            .unwrap(),
        ["a"]
    );
    assert_eq!(
        jsonb_object_keys(sql::<Jsonb>("'{\"a\":1}'::jsonb"))
            .select(jsonb_object_keys::value)
            .load::<String>(connection)
            .unwrap(),
        ["a"]
    );
}

#[diesel_test_helper::test]
fn json_array_functions_load_rows() {
    let connection = &mut connection();
    assert_eq!(
        json_array_elements(sql::<Json>("'[1,null]'::json"))
            .select(json_array_elements::value)
            .load::<serde_json::Value>(connection)
            .unwrap(),
        [serde_json::json!(1), serde_json::Value::Null]
    );
    assert_eq!(
        jsonb_array_elements(sql::<Jsonb>("'[1,null]'::jsonb"))
            .select(jsonb_array_elements::value)
            .load::<serde_json::Value>(connection)
            .unwrap(),
        [serde_json::json!(1), serde_json::Value::Null]
    );
    assert_eq!(
        json_array_elements_text(sql::<Json>("'[1,null]'::json"))
            .select(json_array_elements_text::value)
            .load::<Option<String>>(connection)
            .unwrap(),
        [Some("1".into()), None]
    );
    assert_eq!(
        jsonb_array_elements_text(sql::<Jsonb>("'[1,null]'::jsonb"))
            .select(jsonb_array_elements_text::value)
            .load::<Option<String>>(connection)
            .unwrap(),
        [Some("1".into()), None]
    );
}

#[diesel_test_helper::test]
fn jsonpath_roundtrips_and_queries_every_arity() {
    let connection = &mut connection();
    let path = "$.value";
    let expected = "$.\"value\"";
    assert_eq!(
        diesel::select(path.into_sql::<Jsonpath>())
            .get_result::<String>(connection)
            .unwrap(),
        expected
    );
    assert_eq!(
        diesel::select(path.to_owned().into_sql::<Jsonpath>())
            .get_result::<String>(connection)
            .unwrap(),
        expected
    );
    assert_eq!(
        jsonb_path_query(sql::<Jsonb>("'{\"value\":1}'::jsonb"), path)
            .select(jsonb_path_query::value)
            .load::<serde_json::Value>(connection)
            .unwrap(),
        [serde_json::json!(1)]
    );
    assert_eq!(
        jsonb_path_query_with_vars(
            sql::<Jsonb>("'[1,2]'::jsonb"),
            "$[*] ? (@ == $wanted)",
            sql::<Jsonb>("'{\"wanted\":2}'::jsonb")
        )
        .select(jsonb_path_query::value)
        .load::<serde_json::Value>(connection)
        .unwrap(),
        [serde_json::json!(2)]
    );
    assert_eq!(
        jsonb_path_query_with_silent(
            sql::<Jsonb>("'[1,2]'::jsonb"),
            "$[*] ? (@ == $wanted)",
            sql::<Jsonb>("'{\"wanted\":2}'::jsonb"),
            true
        )
        .select(jsonb_path_query::value)
        .load::<serde_json::Value>(connection)
        .unwrap(),
        [serde_json::json!(2)]
    );
}

#[diesel_test_helper::test]
fn text_functions_load_every_arity() {
    let connection = &mut connection();
    assert_eq!(
        regexp_matches("ab ab", "(a)(b)")
            .select(regexp_matches::value)
            .load::<Vec<Option<String>>>(connection)
            .unwrap(),
        [vec![Some("a".into()), Some("b".into())]]
    );
    assert_eq!(
        regexp_matches_with_flags("ab ab", "(a)(b)", "g")
            .select(regexp_matches::value)
            .load::<Vec<Option<String>>>(connection)
            .unwrap(),
        [
            vec![Some("a".into()), Some("b".into())],
            vec![Some("a".into()), Some("b".into())]
        ]
    );
    assert_eq!(
        regexp_matches("a", "(a)(b)?")
            .select(regexp_matches::value)
            .load::<Vec<Option<String>>>(connection)
            .unwrap(),
        [vec![Some("a".into()), None]]
    );
    assert_eq!(
        regexp_split_to_table("a,b", ",")
            .select(regexp_split_to_table::value)
            .load::<String>(connection)
            .unwrap(),
        ["a", "b"]
    );
    assert_eq!(
        regexp_split_to_table_with_flags("aXb", "x", "i")
            .select(regexp_split_to_table::value)
            .load::<String>(connection)
            .unwrap(),
        ["a", "b"]
    );
    assert_eq!(
        string_to_table("a,b", ",")
            .select(string_to_table::value)
            .load::<Option<String>>(connection)
            .unwrap(),
        [Some("a".into()), Some("b".into())]
    );
    assert_eq!(
        string_to_table_with_null_string("a,NULL", ",", "NULL")
            .select(string_to_table::value)
            .load::<Option<String>>(connection)
            .unwrap(),
        [Some("a".into()), None]
    );
}

#[diesel_test_helper::test]
fn array_functions_load_every_arity() {
    let connection = &mut connection();
    assert_eq!(
        generate_subscripts::<Array<Integer>, _, _>(vec![10, 20], 1)
            .select(generate_subscripts::value)
            .load::<i32>(connection)
            .unwrap(),
        [1, 2]
    );
    assert_eq!(
        generate_subscripts_with_reverse::<Array<Integer>, _, _, _>(vec![10, 20], 1, true)
            .select(generate_subscripts::value)
            .load::<i32>(connection)
            .unwrap(),
        [2, 1]
    );
    assert_eq!(
        unnest::<array_elements::view, Array<Nullable<Integer>>, _>(vec![Some(10), None])
            .select(array_elements::value)
            .load::<Option<i32>>(connection)
            .unwrap(),
        [Some(10), None]
    );
}

#[diesel_test_helper::test]
fn numeric_series_load_every_type_and_arity() {
    let connection = &mut connection();
    assert_eq!(
        generate_series::<integer_series::view, _, _, _>(1, 3)
            .select(integer_series::value)
            .load::<i32>(connection)
            .unwrap(),
        [1, 2, 3]
    );
    assert_eq!(
        generate_series_with_step::<integer_series::view, _, _, _, _>(1, 3, 2)
            .select(integer_series::value)
            .load::<i32>(connection)
            .unwrap(),
        [1, 3]
    );
    assert_eq!(
        generate_series::<bigint_series::view, _, _, _>(1_i64, 3_i64)
            .select(bigint_series::value)
            .load::<i64>(connection)
            .unwrap(),
        [1, 2, 3]
    );
    assert_eq!(
        generate_series_with_step::<bigint_series::view, _, _, _, _>(1_i64, 3_i64, 2_i64)
            .select(bigint_series::value)
            .load::<i64>(connection)
            .unwrap(),
        [1, 3]
    );
    let number = || PgNumeric::Positive {
        weight: 0,
        scale: 0,
        digits: vec![1],
    };
    assert_eq!(
        generate_series::<numeric_series::view, _, _, _>(number(), number())
            .select(numeric_series::value)
            .load::<PgNumeric>(connection)
            .unwrap(),
        [number()]
    );
    assert_eq!(
        generate_series_with_step::<numeric_series::view, _, _, _, _>(number(), number(), number())
            .select(numeric_series::value)
            .load::<PgNumeric>(connection)
            .unwrap(),
        [number()]
    );
}

#[diesel_test_helper::test]
fn timestamp_series_load_every_type_and_arity() {
    let connection = &mut connection();
    let interval = PgInterval {
        microseconds: 1_000_000,
        days: 0,
        months: 0,
    };
    assert_eq!(
        generate_series_with_interval::<timestamp_series::view, _, _, _, _>(
            PgTimestamp(0),
            PgTimestamp(1_000_000),
            interval
        )
        .select(timestamp_series::value)
        .load::<PgTimestamp>(connection)
        .unwrap(),
        [PgTimestamp(0), PgTimestamp(1_000_000)]
    );
    assert_eq!(
        generate_series_with_interval::<timestamptz_series::view, _, _, _, _>(
            PgTimestamp(0),
            PgTimestamp(1_000_000),
            interval
        )
        .select(timestamptz_series::value)
        .load::<PgTimestamp>(connection)
        .unwrap(),
        [PgTimestamp(0), PgTimestamp(1_000_000)]
    );
    assert_eq!(
        generate_series_with_timezone::<timestamptz_series::view, _, _, _, _>(
            PgTimestamp(0),
            PgTimestamp(1_000_000),
            interval,
            "UTC"
        )
        .select(timestamptz_series::value)
        .load::<PgTimestamp>(connection)
        .unwrap(),
        [PgTimestamp(0), PgTimestamp(1_000_000)]
    );
}

#[diesel_test_helper::test]
fn keyword_columns_match_catalog_types() {
    let connection = &mut connection();
    let row = pg_get_keywords()
        .filter(pg_get_keywords::word.eq("select"))
        .get_result::<(String, u8, bool, String, String)>(connection)
        .unwrap();
    assert_eq!(
        row,
        (
            "select".into(),
            b'R',
            true,
            "reserved".into(),
            "can be bare label".into()
        )
    );
}

#[diesel_test_helper::test]
fn builtin_relations_join_user_tables_and_each_other() {
    let connection = &mut connection_with_sean_and_tess_in_users_table();
    let rows = users::table
        .inner_join(
            json_each_text(sql::<Json>("'{\"Sean\":\"one\"}'::json"))
                .on(users::name.eq(json_each_text::key)),
        )
        .select((users::name, json_each_text::value))
        .load::<(String, Option<String>)>(connection)
        .unwrap();
    assert_eq!(rows, [("Sean".into(), Some("one".into()))]);
    let rows = users::table
        .inner_join(
            json_each_text(sql::<Json>("'{\"Sean\":\"one\"}'::json"))
                .on(users::name.eq(json_each_text::key)),
        )
        .inner_join(
            jsonb_each_text(sql::<Jsonb>("'{\"Sean\":\"two\"}'::jsonb"))
                .on(users::name.eq(jsonb_each_text::key)),
        )
        .select((users::name, json_each_text::value, jsonb_each_text::value))
        .load::<(String, Option<String>, Option<String>)>(connection)
        .unwrap();
    assert_eq!(
        rows,
        [("Sean".into(), Some("one".into()), Some("two".into()))]
    );
}

#[diesel_test_helper::test]
fn json_functions_accept_nullable_documents() {
    let connection = &mut connection();
    macro_rules! empty {
        ($function:expr) => {
            assert_eq!($function.count().get_result::<i64>(connection).unwrap(), 0);
        };
    }
    empty!(json_each(sql::<Nullable<Json>>("NULL")));
    empty!(jsonb_each(sql::<Nullable<Jsonb>>("NULL")));
    empty!(json_each_text(sql::<Nullable<Json>>("NULL")));
    empty!(jsonb_each_text(sql::<Nullable<Jsonb>>("NULL")));
    empty!(json_array_elements(sql::<Nullable<Json>>("NULL")));
    empty!(jsonb_array_elements(sql::<Nullable<Jsonb>>("NULL")));
    empty!(json_array_elements_text(sql::<Nullable<Json>>("NULL")));
    empty!(jsonb_array_elements_text(sql::<Nullable<Jsonb>>("NULL")));
    empty!(json_object_keys(sql::<Nullable<Json>>("NULL")));
    empty!(jsonb_object_keys(sql::<Nullable<Jsonb>>("NULL")));
    empty!(jsonb_path_query(
        sql::<Nullable<Jsonb>>("NULL"),
        sql::<Jsonpath>("'$'")
    ));
    empty!(jsonb_path_query_with_vars(
        sql::<Jsonb>("'{}'"),
        sql::<Jsonpath>("'$'"),
        sql::<Nullable<Jsonb>>("NULL")
    ));
    empty!(jsonb_path_query_with_silent(
        sql::<Nullable<Jsonb>>("NULL"),
        sql::<Jsonpath>("'$'"),
        sql::<Jsonb>("'{}'"),
        false
    ));
    assert_eq!(
        json_each_text(sql::<Nullable<Json>>("'{\"a\":1}'::json"))
            .select(json_each_text::value)
            .load::<Option<String>>(connection)
            .unwrap(),
        [Some("1".into())]
    );
}

#[diesel_test_helper::test]
fn return_type_helpers_name_builtin_calls() {
    use diesel::expression::SqlLiteral;

    let connection = &mut connection();
    let keywords: helper_types::pg_get_keywords = pg_get_keywords();
    assert!(keywords.count().get_result::<i64>(connection).unwrap() > 0);

    let elements: helper_types::unnest<array_elements::view, SqlLiteral<Array<Nullable<Integer>>>> =
        unnest(sql::<Array<Nullable<Integer>>>("ARRAY[1,NULL]::integer[]"));
    assert_eq!(
        elements
            .select(array_elements::value)
            .load::<Option<i32>>(connection)
            .unwrap(),
        [Some(1), None]
    );
    let subscripts: helper_types::generate_subscripts<
        SqlLiteral<Array<Integer>>,
        SqlLiteral<Integer>,
    > = generate_subscripts(sql::<Array<Integer>>("ARRAY[1,2]"), sql::<Integer>("1"));
    assert_eq!(
        subscripts
            .select(generate_subscripts::value)
            .load::<i32>(connection)
            .unwrap(),
        [1, 2]
    );
    let series: helper_types::generate_series<
        integer_series::view,
        SqlLiteral<Integer>,
        SqlLiteral<Integer>,
    > = generate_series(sql::<Integer>("1"), sql::<Integer>("2"));
    assert_eq!(
        series
            .select(integer_series::value)
            .load::<i32>(connection)
            .unwrap(),
        [1, 2]
    );
}
