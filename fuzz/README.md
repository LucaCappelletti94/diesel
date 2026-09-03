# diesel-fuzz

Fuzz harnesses for diesel's deserialization code, reaching diesel only through its public API. Every finding is a `Violation` variant, so the panic message names its class.

```
cargo +nightly fuzz run <target>
```

Seeds are checked in; regenerate with `cargo test --test corpus -- --ignored`.

## Targets

| Target | Property |
|---|---|
| `jsonb_decode` | decoding never panics |
| `jsonb_decode_oracle` | diesel and sqlite agree; an accept-invalid has a known class |
| `jsonb_strictness` | a reject-valid has a known class |
| `jsonb_encode_roundtrip` | diesel's blob is valid JSONB and reads back unchanged, for the document the input spells |
| `jsonb_structured` | the decode properties, grammar-fed |
| `pg_from_sql` | 42 postgres decoders never panic |
| `pg_differential` | chrono against time, ipnet against ipnetwork, `PgNumeric` round trip |
| `mysql_from_sql` | 29 mysql decoders never panic, under every wire type |
| `mysql_differential` | chrono against time on the same `MYSQL_TIME` |
| `sqlite_text_datetime` | chrono against time on the same text |

A differential target reports a value mismatch and a one-sided decode alike. A
one-sided decode is explained only where the refusing library's own range stops
short, which for `time` is year ±9999.

A jsonb divergence is only excused once removing the known feature removes the
divergence: `leniency::repair` parses the blob strictly and rewrites every known
feature away, and `properties::agree` requires diesel and sqlite to read the
same value from the result, not merely to accept it. Every class removed is
reported, since one alone need not account for the divergence. A
sibling's `INT5` therefore cannot cover for a novel failure, and a structural
cause is never mistaken for a leniency.

A seed is only meaningful where the target parses its bytes. `jsonb_structured`, both mysql targets and both postgres targets take `Arbitrary` input, so libFuzzer feeds a file to them as entropy and a hand-written seed would decode to something unrelated; only their own fuzzer-grown corpora belong there.

## Notes

`src/jsonb/` splits the wire format, the generator, the leniency classes and the properties; `src/differential.rs` holds the comparison keys the postgres, mysql and sqlite date/time properties share.

Minimize a crash with `cargo fuzz tmin`, then pin it as an inline `#[diesel_test_helper::test]` case in the module that owns the code.

`-max_len=4096` is deliberate: unbounded input rediscovers the stack overflow `serde_json::Value` shows while being dropped.

Sqlite's JSONB format is internal, so an oracle disagreement after a `libsqlite3-sys` bump is not automatically a diesel bug.

A reported bug is skipped by the narrowest guard that names it, never by dropping its target: `jsonb::has_known_panic` (the header-arithmetic panic), `jsonb::has_known_reader_defect` (it, plus accepted trailing bytes), `jsonb::explains_divergence` (the seven reader classes), `jsonb::known_writer_defect` (three value shapes), `pg::known_panic` (two interval panics), `mysql::known_validation_split` and its two field predicates, and `datetime::explains_text_divergence`. Each has a witness test that fails once the bug is fixed, and every guard names the input it skips rather than the target.

`enabled_targets.txt` names the targets CI runs, read by both the fuzz workflow and the ClusterFuzzLite build; all ten are enabled.

ClusterFuzzLite owns scheduled fuzzing and the corpus it grows. `fuzz.yml` tests the harness on every change and fuzzes from the checked-in seeds only on manual dispatch, so no second corpus accumulates.
