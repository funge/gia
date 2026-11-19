#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
lake build HardwareQuotientProgram:static HardwareEvaluatorProgram:static HardwareAffineProductProgram:static HardwareAffineProgram:static TrigHalvingProgram:static SplitReductionProgram:static DyadicReductionProgram:static HardwareAddition HardwareSubtraction HardwareMultiplication HardwareDivision HardwareSquareRoot SineProgram:static SineReductionProgram:static CosineProgram:static QuadrantProgram:static HardwareBounds:static
out="$(mktemp -d)"
trap 'rm -rf "$out"' EXIT
lake env lean -c "$out/Main.c" hardware/Main.lean
bash hardware/build_core.sh "$out"
"${CC:-cc}" -O2 -frounding-math -fno-fast-math -ffp-contract=off -fno-math-errno \
  -I "$(lean --print-prefix)/include" -c hardware/adapter.c -o "$out/adapter.o"
leanc "$out/Main.c" "$out/adapter.o" "$out/directed_core.o" .lake/build/lib/libHardwareQuotientProgram.a .lake/build/lib/libHardwareEvaluatorProgram.a .lake/build/lib/libHardwareAffineProductProgram.a .lake/build/lib/libHardwareAffineProgram.a .lake/build/lib/libHardwareBounds.a .lake/build/lib/libSineProgram.a .lake/build/lib/libSineReductionProgram.a .lake/build/lib/libCosineProgram.a .lake/build/lib/libQuadrantProgram.a .lake/build/lib/libDyadicReductionProgram.a .lake/build/lib/libSplitReductionProgram.a .lake/build/lib/libTrigHalvingProgram.a \
  -lm -o "$out/hardware-add"
"$out/hardware-add" | tee "$out/native-output.txt"
python3 hardware/check_sine.py "$out/native-output.txt"
python3 hardware/check_reduction.py "$out/native-output.txt"
python3 hardware/check_quadrants.py "$out/native-output.txt"
python3 hardware/check_global.py "$out/native-output.txt"
python3 hardware/check_dyadic.py "$out/native-output.txt"
python3 hardware/check_split.py "$out/native-output.txt"
python3 hardware/check_halving.py "$out/native-output.txt"
python3 hardware/check_affine.py "$out/native-output.txt"
python3 hardware/check_affine_product.py "$out/native-output.txt"
python3 hardware/check_evaluator.py "$out/native-output.txt"
python3 hardware/check_quotient.py "$out/native-output.txt"
