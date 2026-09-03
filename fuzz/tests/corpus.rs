//! Regenerates the seed corpora: `cargo test --test corpus -- --ignored`.

use diesel_fuzz::sqlite::{text_to_jsonb, with_conn};
use std::path::Path;

const DOCUMENTS: &[&str] = &[
    "null",
    "true",
    "false",
    "0",
    "-9223372036854775808",
    "9223372036854775807",
    "18446744073709551615",
    "1.5",
    "1.5e300",
    "1e-7",
    "\"\"",
    "\"a\"",
    "\"\\u0000\\u001f\\\"\\\\\"",
    "\"\\ud83d\\ude00\"",
    "[]",
    "{}",
    "[null,true,1,\"a\",[],{}]",
    "{\"a\":1}",
    "{\"\":null}",
    "[1,[2,[3,[4,[5]]]]]",
    "{\"a\":{\"b\":{\"c\":{\"d\":1}}}}",
    "[[[[[[[[[[1]]]]]]]]]]",
    "{\"dup\":1,\"dup\":2}",
];

/// Blobs no encoder produces; each names a divergence class.
const HAND_WRITTEN: &[&[u8]] = &[
    &[0x10, 0x00],
    &[0x11, 0x08],
    &[0x17, 0x0D],
    &[0x23, b'4', b' '],
    &[0x24, b'0', b'x', b'1', b'f'],
    &[0x2C, 0x17, b'a'],
    &[0x3B, 0x1B, 0x1B, 0x00],
];

const TIMESTAMPS: &[&str] = &[
    "2026-09-03",
    "2026-09-03 12:34:56",
    "2026-09-03T12:34:56.123456",
    "2026-09-03 12:34:56+02:00",
    "12:34:56",
    "12:34:56.123",
    "-4712-01-01",
    "9999-12-31 23:59:59.999999Z",
];

fn write(target: &str, name: &str, bytes: &[u8]) {
    let dir = Path::new("corpus").join(target);
    std::fs::create_dir_all(&dir).expect("corpus directory");
    std::fs::write(dir.join(name), bytes).expect("corpus file");
}

#[test]
#[ignore = "writes to the corpus directories"]
fn write_seed_corpus() {
    with_conn(|conn| {
        for (index, document) in DOCUMENTS.iter().enumerate() {
            let blob = text_to_jsonb(conn, document).expect("valid json");
            for target in ["jsonb_decode", "jsonb_decode_oracle", "jsonb_strictness"] {
                write(target, &format!("sqlite{index:02}"), &blob);
            }
            write(
                "jsonb_encode_roundtrip",
                &format!("json{index:02}"),
                document.as_bytes(),
            );
        }
    });
    for (index, blob) in HAND_WRITTEN.iter().enumerate() {
        for target in ["jsonb_decode", "jsonb_decode_oracle", "jsonb_strictness"] {
            write(target, &format!("class{index:02}"), blob);
        }
    }
    for (index, text) in TIMESTAMPS.iter().enumerate() {
        write(
            "sqlite_text_datetime",
            &format!("text{index:02}"),
            text.as_bytes(),
        );
    }
}

/// What a target's `fuzz_target!` closure takes, which decides what a seed means.
enum Input {
    /// `&[u8]`, so a seed is the byte string itself.
    Bytes,
    /// `&str`, so a seed is its text.
    Text,
    /// A json document parsed from the bytes.
    Json,
    /// `Arbitrary`, so a seed is entropy and a hand-written one would decode to
    /// something unrelated.
    Entropy,
}

/// Every target: what it takes, and why it is disabled if it is. The set CI
/// runs lives in `enabled_targets.txt`, and the tests below tie the two
/// together so a new target cannot be forgotten by either.
struct Target {
    name: &'static str,
    input: Input,
    disabled: Option<&'static str>,
}

const fn target(name: &'static str, input: Input, disabled: Option<&'static str>) -> Target {
    Target {
        name,
        input,
        disabled,
    }
}

const TARGETS: &[Target] = &[
    target("jsonb_decode", Input::Bytes, None),
    target("jsonb_decode_oracle", Input::Bytes, None),
    target("jsonb_strictness", Input::Bytes, None),
    target("jsonb_encode_roundtrip", Input::Json, None),
    target("jsonb_structured", Input::Entropy, None),
    target("pg_from_sql", Input::Entropy, None),
    target("pg_differential", Input::Entropy, None),
    target("mysql_from_sql", Input::Entropy, None),
    target("mysql_differential", Input::Entropy, None),
    target("sqlite_text_datetime", Input::Text, None),
];

fn enabled_targets() -> std::collections::BTreeSet<String> {
    std::fs::read_to_string("enabled_targets.txt")
        .expect("the enabled list")
        .lines()
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .map(str::to_owned)
        .collect()
}

fn target_files() -> std::collections::BTreeSet<String> {
    std::fs::read_dir("fuzz_targets")
        .expect("the target directory")
        .map(|entry| {
            entry
                .expect("a target")
                .path()
                .file_stem()
                .expect("a file stem")
                .to_string_lossy()
                .into_owned()
        })
        .collect()
}

/// Every target is registered, built, and either enabled or disabled with a
/// reason: a new one cannot slip past CI by being listed nowhere.
#[test]
fn every_target_is_accounted_for() {
    let files = target_files();
    let registered: std::collections::BTreeSet<String> = TARGETS
        .iter()
        .map(|target| target.name.to_owned())
        .collect();
    assert_eq!(files, registered, "the registry and fuzz_targets/ disagree");

    let manifest = std::fs::read_to_string("Cargo.toml").expect("the manifest");
    for target in TARGETS {
        assert!(
            manifest.contains(&format!("name = \"{}\"", target.name)),
            "{} has no [[bin]]",
            target.name
        );
    }

    let enabled = enabled_targets();
    let disabled: std::collections::BTreeSet<String> = TARGETS
        .iter()
        .filter(|target| target.disabled.is_some())
        .map(|target| target.name.to_owned())
        .collect();
    assert!(
        enabled.is_disjoint(&disabled),
        "a target is both enabled and disabled"
    );
    assert_eq!(
        enabled
            .union(&disabled)
            .cloned()
            .collect::<std::collections::BTreeSet<_>>(),
        registered,
        "a target is neither enabled nor disabled with a reason"
    );
}

/// A curated seed only means anything where the target parses it, so an
/// `Arbitrary` target must hold none: libFuzzer would feed it as entropy.
#[test]
fn seeds_match_their_target_input() {
    let curated: std::collections::BTreeSet<Vec<u8>> = with_conn(|conn| {
        DOCUMENTS
            .iter()
            .map(|document| text_to_jsonb(conn, document).expect("valid json"))
            .chain(
                DOCUMENTS
                    .iter()
                    .map(|document| document.as_bytes().to_vec()),
            )
            .chain(HAND_WRITTEN.iter().map(|blob| blob.to_vec()))
            .chain(TIMESTAMPS.iter().map(|text| text.as_bytes().to_vec()))
            .collect()
    });

    for Target { name, input, .. } in TARGETS {
        let dir = Path::new("corpus").join(name);
        // an absent directory is a missing corpus, not an empty one
        let seeds: Vec<Vec<u8>> = std::fs::read_dir(&dir)
            .unwrap_or_else(|error| panic!("{name} has no corpus: {error}"))
            .map(|seed| std::fs::read(seed.expect("a seed").path()).expect("seed bytes"))
            .collect();
        assert!(!seeds.is_empty(), "{name} has no seeds");
        match input {
            Input::Entropy => {
                for seed in &seeds {
                    assert!(
                        !curated.contains(seed),
                        "{name} takes entropy, so this seed decodes to something else"
                    );
                }
            }
            Input::Bytes => {}
            Input::Text => {
                for seed in &seeds {
                    assert!(str::from_utf8(seed).is_ok(), "{name} seed is not utf-8");
                }
            }
            Input::Json => {
                for seed in &seeds {
                    serde_json::from_slice::<serde_json::Value>(seed)
                        .unwrap_or_else(|error| panic!("{name} seed is not json: {error}"));
                }
            }
        }
    }
}

/// Every corpus directory names a target, and every seed reaches `$OUT` as a zip.
#[test]
fn package_corpora_writes_one_zip_per_target() {
    let out = std::env::temp_dir().join(format!("diesel-fuzz-out-{}", std::process::id()));
    std::fs::create_dir_all(&out).expect("an output directory");
    let status = std::process::Command::new("bash")
        .arg(".clusterfuzzlite/package_corpora.sh")
        .current_dir("..")
        .env("OUT", &out)
        .status()
        .expect("bash runs");
    assert!(status.success(), "packaging failed");

    for entry in std::fs::read_dir("corpus").expect("the corpus directory") {
        let dir = entry.expect("a corpus entry").path();
        let target = dir.file_name().expect("a directory name").to_owned();
        assert!(
            Path::new("fuzz_targets")
                .join(&target)
                .with_extension("rs")
                .exists(),
            "{target:?} is not a fuzz target"
        );
        let seeds: std::collections::BTreeSet<String> = std::fs::read_dir(&dir)
            .expect("seeds")
            .map(|seed| {
                seed.expect("a seed")
                    .file_name()
                    .to_string_lossy()
                    .into_owned()
            })
            .collect();
        assert!(!seeds.is_empty(), "{target:?} has no seeds");

        let zip = out.join(format!("{}_seed_corpus.zip", target.to_string_lossy()));
        let listed = std::process::Command::new("unzip")
            .arg("-Z1")
            .arg(&zip)
            .output()
            .expect("unzip runs");
        let packed: std::collections::BTreeSet<String> = String::from_utf8(listed.stdout)
            .expect("utf-8 listing")
            .lines()
            .map(str::to_owned)
            .collect();
        assert_eq!(packed, seeds, "{target:?} is not packaged as {zip:?}");
    }
    std::fs::remove_dir_all(&out).expect("cleanup");
}

/// Only the enabled targets reach `$OUT`, so no known-red target is fuzzed in CI.
#[test]
fn export_targets_copies_exactly_the_enabled_list() {
    let root = std::env::temp_dir().join(format!("diesel-fuzz-export-{}", std::process::id()));
    let built = root.join("built");
    let out = root.join("out");
    std::fs::create_dir_all(&built).expect("a build directory");
    std::fs::create_dir_all(&out).expect("an output directory");

    let mut all = Vec::new();
    for entry in std::fs::read_dir("fuzz_targets").expect("the target directory") {
        let target = entry.expect("a target").path();
        let name = target
            .file_stem()
            .expect("a file stem")
            .to_string_lossy()
            .into_owned();
        std::fs::write(built.join(&name), b"stub").expect("a stub binary");
        all.push(name);
    }

    let status = std::process::Command::new("bash")
        .arg(".clusterfuzzlite/export_targets.sh")
        .current_dir("..")
        .env("OUT", &out)
        .env("TARGET_DIR", &built)
        .status()
        .expect("bash runs");
    assert!(status.success(), "export failed");

    let exported: std::collections::BTreeSet<String> = std::fs::read_dir(&out)
        .expect("the output directory")
        .map(|entry| {
            entry
                .expect("an exported file")
                .file_name()
                .to_string_lossy()
                .into_owned()
        })
        .collect();
    let enabled = enabled_targets();

    assert_eq!(exported, enabled);
    assert!(
        enabled.iter().all(|name| all.contains(name)),
        "an unknown target is enabled"
    );
    assert!(
        !enabled.is_empty(),
        "the list must name at least one target"
    );
    std::fs::remove_dir_all(&root).expect("cleanup");
}
