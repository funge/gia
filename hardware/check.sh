#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
lake build HardwareAddition HardwareSubtraction HardwareMultiplication HardwareDivision HardwareBounds:static
out="$(mktemp -d)"
trap 'rm -rf "$out"' EXIT
lake env lean -c "$out/Main.c" hardware/Main.lean
cc -O2 -frounding-math -fno-fast-math -ffp-contract=off \
  -I "$(lean --print-prefix)/include" -c hardware/adapter.c -o "$out/adapter.o"
objdump -d "$out/adapter.o" > "$out/disassembly.txt"
grep -q addsd "$out/disassembly.txt"
grep -q subsd "$out/disassembly.txt"
grep -q mulsd "$out/disassembly.txt"
grep -q divsd "$out/disassembly.txt"
printf "Verified hardware addsd, subsd, mulsd and divsd in adapter object\n"
leanc "$out/Main.c" "$out/adapter.o" .lake/build/lib/libHardwareBounds.a \
  -lm -o "$out/hardware-add"
"$out/hardware-add"
