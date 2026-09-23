#![no_main]
//! Sqlite must answer the sql diesel renders as it answers the fully parenthesised tree.

use diesel_fuzz::query::{Input, sqlite};
use libfuzzer_sys::fuzz_target;

fuzz_target!(|input: Input| {
    let checked = match &input {
        Input::Rows(query) => sqlite::check(query),
        Input::Groups(tree) => sqlite::check_grouped(tree),
    };
    if let Err(violation) = checked {
        panic!("{violation}");
    }
});
