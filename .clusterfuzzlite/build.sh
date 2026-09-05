#!/bin/bash
# the caller may invoke this with `bash build.sh`, which ignores the shebang
set -eu

cd "$SRC/diesel"
# the base image exports its own dated nightly as RUSTUP_TOOLCHAIN, which
# already overrides the rust-toolchain pin, so naming a toolchain here would
# fail on one it never installed
cargo fuzz build -O --fuzz-dir fuzz

# asking cargo-fuzz for the names, so adding a target needs no change here, and
# holding them in a variable, since a pipeline would hide the command failing
targets=$(cargo fuzz list --fuzz-dir fuzz)
if [ -z "$targets" ]; then
    echo "cargo fuzz list named no target" >&2
    exit 1
fi

target_dir=fuzz/target/x86_64-unknown-linux-gnu/release
for name in $targets; do
    cp "$target_dir/$name" "$OUT/"
done

# the layout cifuzz unpacks before fuzzing, for the targets that have seeds
for dir in fuzz/corpus/*/; do
    name=$(basename "$dir")
    zip -j -q "$OUT/${name}_seed_corpus.zip" "$dir"*
done
