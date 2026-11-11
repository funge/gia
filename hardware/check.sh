#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
lake build SplitReductionProgram:static DyadicReductionProgram:static HardwareAddition HardwareSubtraction HardwareMultiplication HardwareDivision HardwareSquareRoot SineProgram:static SineReductionProgram:static CosineProgram:static QuadrantProgram:static HardwareBounds:static
out="$(mktemp -d)"
trap 'rm -rf "$out"' EXIT
lake env lean -c "$out/Main.c" hardware/Main.lean
cc -O2 -frounding-math -fno-fast-math -ffp-contract=off -fno-math-errno \
  -I "$(lean --print-prefix)/include" -c hardware/adapter.c -o "$out/adapter.o"
objdump -d "$out/adapter.o" > "$out/disassembly.txt"
grep -q addsd "$out/disassembly.txt"
grep -q subsd "$out/disassembly.txt"
grep -q mulsd "$out/disassembly.txt"
grep -q divsd "$out/disassembly.txt"
grep -q sqrtsd "$out/disassembly.txt"
if nm -u "$out/adapter.o" | grep -q sqrt; then
  echo "Unexpected library sqrt call" >&2
  exit 1
fi
printf "Verified hardware addsd, subsd, mulsd, divsd and sqrtsd in adapter object\n"
leanc "$out/Main.c" "$out/adapter.o" .lake/build/lib/libHardwareBounds.a .lake/build/lib/libSineProgram.a .lake/build/lib/libSineReductionProgram.a .lake/build/lib/libCosineProgram.a .lake/build/lib/libQuadrantProgram.a .lake/build/lib/libDyadicReductionProgram.a .lake/build/lib/libSplitReductionProgram.a \
  -lm -o "$out/hardware-add"
"$out/hardware-add" | tee "$out/native-output.txt"
python3 hardware/check_sine.py "$out/native-output.txt"
python3 hardware/check_reduction.py "$out/native-output.txt"
python3 hardware/check_quadrants.py "$out/native-output.txt"
python3 hardware/check_global.py "$out/native-output.txt"
python3 hardware/check_dyadic.py "$out/native-output.txt"
python3 hardware/check_split.py "$out/native-output.txt"
