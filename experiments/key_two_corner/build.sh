#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.."
mkdir -p experiments/key_two_corner/out
out=experiments/key_two_corner/out
# Uses unchanged production build flags and core, including native fault controls.
bash hardware/build_core.sh "$out"
flags=(-std=c11 -O2 -frounding-math -fno-fast-math -ffp-contract=off -fno-math-errno)
"${CC:-cc}" "${flags[@]}" -I "$(lean --print-prefix)/include" -c hardware/adapter.c -o "$out/adapter.o"
"${CC:-cc}" "${flags[@]}" -I "$(lean --print-prefix)/include" -c experiments/key_two_corner/environment.c -o "$out/environment.o"
lake build keyCornerExperiment
python3 experiments/key_two_corner/qualify.py
