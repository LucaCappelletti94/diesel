#![no_main]
//! Postgres must read the operator nesting diesel meant, and sqlite must answer the sql diesel
//! renders as it answers the fully parenthesised tree.

use diesel_fuzz::query::{Input, pg, sqlite};
use libfuzzer_sys::fuzz_target;

fuzz_target!(|input: Input| {
    match &input {
        Input::Rows(query) => {
            if let Err(violation) = pg::check(query) {
                panic!("{violation}");
            }
            if let Err(violation) = sqlite::check(query) {
                panic!("{violation}");
            }
        }
        Input::Groups(tree) => {
            if let Err(violation) = pg::check_grouped(tree) {
                panic!("{violation}");
            }
            if let Err(violation) = sqlite::check_grouped(tree) {
                panic!("{violation}");
            }
        }
    }
});
