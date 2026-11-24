#!/usr/bin/env bash
# Opt-in source-algorithm check; no native floating-point backend or timing.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.."
lake build AccuracySearchExample
out="$(mktemp -d)"
trap 'rm -rf "$out"' EXIT
# Compile generated C to objects; this is not a linked native executable.
lake env lean -c "$out/Main.c" experiments/accuracy_search/Main.lean
leanc -c .lake/build/ir/ExpressionStreams.c -o "$out/ExpressionStreams.o"
leanc -c "$out/Main.c" -o "$out/Main.o"
lake env lean --run experiments/accuracy_search/Main.lean
