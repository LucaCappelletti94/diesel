FROM gcr.io/oss-fuzz-base/base-builder-rust
# pg_query's build script runs bindgen, which needs libclang
RUN apt-get update && apt-get install -y --no-install-recommends libclang-dev && rm -rf /var/lib/apt/lists/*
COPY . $SRC/diesel
WORKDIR $SRC/diesel
COPY ./.clusterfuzzlite/build.sh $SRC/
