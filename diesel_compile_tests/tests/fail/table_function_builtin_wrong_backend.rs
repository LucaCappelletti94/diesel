extern crate diesel;

use diesel::pg::table_functions::pg_get_keywords;
use diesel::prelude::*;
use diesel::sqlite::table_functions::pragma_table_info;

fn main() {
    let sqlite_connection = &mut SqliteConnection::establish(":memory:").unwrap();
    pg_get_keywords()
        .select(pg_get_keywords::word)
        .load::<String>(sqlite_connection)
        //~^ ERROR: no valid SQL fragment for the `Sqlite` backend
        .unwrap();

    let postgres_connection = &mut PgConnection::establish("").unwrap();
    pragma_table_info("users")
        .select(pragma_table_info::name)
        .load::<String>(postgres_connection)
        //~^ ERROR: no valid SQL fragment for the `Pg` backend
        .unwrap();
}
