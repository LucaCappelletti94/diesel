## The `crate` attribute

`#[diesel(crate = path::to::diesel)]` names the path this derive's output
reaches diesel by. Without it the output uses `::diesel`, which resolves
through the extern prelude, so a module or item named `diesel` in scope does
not disturb it, but the dependency does have to be named `diesel`.

A `macro_rules!` macro that generates diesel items passes on the path it
reached diesel by, so its expansion also works in a crate that renames the
dependency or does not depend on diesel directly:

```rust
# pub extern crate diesel;
#[doc(hidden)]
pub mod __deps {
    pub use diesel;
}

macro_rules! define_user {
    () => {
        #[derive($crate::__deps::diesel::Insertable)]
        #[diesel(crate = $crate::__deps::diesel, table_name = users)]
        pub struct User {
            pub id: i32,
        }
    };
}
# fn main() {}
```
