FROM gcr.io/oss-fuzz-base/base-builder-rust
COPY . $SRC/diesel-fuzz
WORKDIR $SRC/diesel-fuzz
COPY ./.clusterfuzzlite/build.sh $SRC/
