#!/bin/bash -eu

cd "$SRC/diesel-fuzz"
# the base image exports its own dated nightly as RUSTUP_TOOLCHAIN, which
# already overrides the rust-toolchain pin; naming a toolchain it never
# installed would fail the build
cargo fuzz build -O --fuzz-dir fuzz

.clusterfuzzlite/export_targets.sh
.clusterfuzzlite/package_corpora.sh
