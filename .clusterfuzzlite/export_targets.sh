#!/bin/bash -eu

# a target red against main would read as a novel crash on every pull request
target_dir=${TARGET_DIR:-fuzz/target/x86_64-unknown-linux-gnu/release}
grep -v '^#' fuzz/enabled_targets.txt | while read -r name; do
    [ -n "$name" ] || continue
    cp "$target_dir/$name" "$OUT/"
done
