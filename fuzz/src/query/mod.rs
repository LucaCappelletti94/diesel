//! Random expression trees built through diesel's query builder, for checking the sql it renders
//! against sqlite's own evaluation.

mod tree;

pub use tree::*;

diesel::table! {
    t (id) {
        id -> Integer,
        a -> Integer,
        b -> Nullable<Integer>,
        s -> Text,
        n -> Nullable<Text>,
        f -> Bool,
        g -> Nullable<Integer>,
        j -> Nullable<Json>,
    }
}

pub mod sqlite;
