"""Require scalar binary64 instructions in the actual native core object."""
from pathlib import Path
import re
import sys

if not __debug__:
    raise SystemExit("Qualification requires Python assertions enabled (no -O/PYTHONOPTIMIZE)")

disassembly, arch = sys.argv[1:]
asm = Path(disassembly).read_text()
fmt = "\n".join(line for line in asm.splitlines() if "file format" in line)
if arch in {"arm64", "aarch64"}:
    assert re.search(r"aarch64|arm64", fmt), "Core object is not native AArch64"
    patterns = [rf"\b{op}\s+d\d+,\s*d\d+" + (r",\s*d\d+" if op != "fsqrt" else "")
                for op in ("fadd", "fsub", "fmul", "fdiv", "fsqrt")]
elif arch == "x86_64":
    assert re.search(r"x86[-_:]64|i386:x86-64", fmt), "Core object is not native x86_64"
    patterns = [rf"\b{op}sd\b" for op in ("add", "sub", "mul", "div", "sqrt")]
else:
    raise SystemExit(f"Unqualified native architecture: {arch}")
for pattern in patterns:
    assert re.search(pattern, asm), f"Missing scalar binary64 instruction: {pattern}"
print(f"Verified native {arch} scalar binary64 add/subtract/multiply/divide/sqrt instructions")
