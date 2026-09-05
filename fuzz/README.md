# diesel-fuzz

Fuzz harnesses for diesel's deserialization code, reaching diesel only through its public API.

```
cargo +nightly fuzz run --fuzz-dir fuzz <target>   # from the repository root
```

| Target | Property |
|---|---|
| `pg_from_sql` | 48 postgres decoders never panic |
| `mysql_from_sql` | 29 mysql decoders never panic, under every wire type |
| `sqlite_from_sql` | 26 sqlite decoders never panic, in every storage class a value can carry |
| `sqlite_jsonb_decode` | decoding a blob never panics |
| `sqlite_jsonb_roundtrip` | diesel reads back what it wrote as jsonb and as json text, unchanged, and sqlite calls both well formed |

Every target is fuzzed and expected to pass: nothing here is skipped, excused or classified. The
workflow builds and tests the harness on every change and fuzzes on request. A follow-up pull
request adds ClusterFuzzLite, which then owns the scheduled and pull request runs.

Seeds are checked in for `sqlite_jsonb_decode`, which parses its input as a blob. The other four
targets take `Arbitrary` input, so libFuzzer feeds a file to them as entropy and a hand-written
seed would decode to something unrelated.

`sqlite_jsonb_roundtrip` builds its document from entropy rather than parsing json: the reader
parses with `serde_json` as well, so a parsed input makes both sides round a float the same way and
the round trip agrees on a value neither spells correctly.

`-max_len=4096` is deliberate: unbounded input rediscovers the stack overflow
`serde_json::Value` shows while being dropped.

Minimize a crash with `cargo fuzz tmin`, then pin it as a test in the diesel module that owns the
code.
