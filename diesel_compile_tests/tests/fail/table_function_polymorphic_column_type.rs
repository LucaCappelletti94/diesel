extern crate diesel;

use diesel::prelude::*;
use diesel::sql_types::Integer;

view! {
    text_series {
        value -> Text,
    }
}

fn main() {
    let _ = diesel::pg::table_functions::generate_series::<text_series::view, Integer, _, _>(1, 3);
    //~^ ERROR: type mismatch resolving `<view as SingleColumnRelation>::ColumnSqlType == Integer`
}
