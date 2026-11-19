#!/usr/bin/env bash
# Shared compilation contract for both standalone and compiled-Lean checks.
set -euo pipefail
out="$1"
cc="${CC:-cc}"
flags=(-std=c11 -O2 -frounding-math -fno-fast-math -ffp-contract=off -fno-math-errno)
"$cc" "${flags[@]}" -c hardware/directed_core.c -o "$out/directed_core.o"
objdump -d "$out/directed_core.o" > "$out/disassembly.txt"
python3 hardware/check_instructions.py "$out/disassembly.txt" "$(uname -m)"
nm -u "$out/directed_core.o" > "$out/undefined-symbols.txt"
if grep -E '(^|[[:space:]])_?sqrt([[:space:]@]|$)' "$out/undefined-symbols.txt"; then
  echo "Unexpected library sqrt call" >&2
  exit 1
fi
"$cc" "${flags[@]}" hardware/check_native.c "$out/directed_core.o" -lm -o "$out/check-native"
"$out/check-native" --environment | tee "$out/environment.txt"
python3 hardware/check_native.py "$out/check-native" "$out/native-core-output.txt"
"$cc" "${flags[@]}" -Dfeholdexcept=gia_test_feholdexcept \
  -Dfesetround=gia_test_fesetround -Dfesetenv=gia_test_fesetenv \
  -c hardware/directed_core.c -o "$out/fault-core.o"
"$cc" "${flags[@]}" hardware/check_faults.c "$out/fault-core.o" -lm -o "$out/check-faults"
"$out/check-faults" | tee "$out/faults.txt"
