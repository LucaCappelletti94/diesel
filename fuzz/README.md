# diesel-fuzz

Fuzz harnesses for diesel's deserialization code and query builder, reaching diesel only through its public API.

```
cargo +nightly fuzz run --fuzz-dir fuzz <target>   # from the repository root
```

| Target | Property |
|---|---|
| `pg_from_sql` | 48 postgres decoders never panic |
| `mysql_from_sql` | 29 mysql decoders never panic, under every wire type |
| `sqlite_from_sql` | 26 sqlite decoders never panic, in every storage class |
| `sqlite_jsonb_decode` | decoding a blob never panics |
| `sqlite_jsonb_roundtrip` | diesel reads back what it wrote as jsonb and json text, and sqlite calls both valid |
| `query_builder` | postgres parses each plain and grouped `SELECT` diesel builds into the operator tree the fuzzer meant, and sqlite answers it as it answers the fully parenthesised tree |

- Only `sqlite_jsonb_decode` has a checked-in corpus; the other targets take `Arbitrary` input.
- `sqlite_jsonb_roundtrip` builds its value from entropy, not parsed `JSON`, so a writer bug cannot hide behind matched `serde_json` rounding.
- `query_builder` leaves mysql out because no mysql parser runs in process.
- `-max_len=4096` avoids the drop-time stack overflow in `serde_json::Value`.
- Minimize a crash with `cargo fuzz tmin`, then pin it as a test in the owning diesel module.
