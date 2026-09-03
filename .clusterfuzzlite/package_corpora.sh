#!/bin/bash -eu

# the layout cifuzz unpacks before fuzzing
for dir in fuzz/corpus/*/; do
    name=$(basename "$dir")
    rm -f "$OUT/${name}_seed_corpus.zip"
    zip -j -q "$OUT/${name}_seed_corpus.zip" "$dir"*
done
