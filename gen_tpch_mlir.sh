#!/bin/bash

if [ "$#" -ne 1 ]; then
  echo "Usage: $0 <out_dir>"
  echo "Example: $0 ../scair/tests/filecheck/dialects/sdql/tpch-gen"
  exit 2
fi

OUT_DIR="$1"
mkdir -p "$OUT_DIR"

failed=""

for i in $(seq 1 22); do
  q="q$i"
  out="$OUT_DIR/$q.mlir"

  echo "Generating $q... -> $out"
  sbt --error "run to_mlir progs/tpch $q.sdql" > "$out" 2>&1

  if [ $? -ne 0 ]; then
    echo "  FAILED (see $out)"
    failed="$failed $q"
  fi
done

if [ -n "$failed" ]; then
  echo "Done, failures:$failed"
  exit 1
else
  echo "Done. Wrote files to: $OUT_DIR"
fi
