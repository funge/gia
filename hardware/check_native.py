"""Independent exact-rational oracle for the shared binary64 C core.

Finite output is checked for enclosure and tight directed endpoints. This is
empirical adapter evidence, not a proof of the C/compiler/hardware contract.
"""
from fractions import Fraction
from pathlib import Path
import random
import subprocess
import sys

if not __debug__:
    raise SystemExit("Qualification requires Python assertions enabled (no -O/PYTHONOPTIMIZE)")

SIGN = 1 << 63
MAX = 0x7FEFFFFFFFFFFFFF


def decode(bits):
    exponent = (bits >> 52) & 0x7FF
    if exponent == 0x7FF:
        return None
    mantissa = bits & ((1 << 52) - 1)
    if exponent:
        mantissa += 1 << 52
    power = exponent - 1075 if exponent else -1074
    return (-1 if bits & SIGN else 1) * Fraction(mantissa) * Fraction(2) ** power


def neighbor(bits, upward):
    if bits & ~SIGN == 0:
        return 1 if upward else SIGN | 1
    return bits + (1 if upward != bool(bits & SIGN) else -1)


def verify(vector, success, lower, upper):
    op, ab, bb = vector
    a, b = decode(ab), decode(bb)
    invalid = a is None or b is None or op not in range(5)
    invalid |= op == 3 and b == 0
    invalid |= op == 4 and a is not None and a < 0
    if invalid:
        assert not success, ("invalid accepted", vector)
        return
    if op == 4:
        assert success, ("sqrt unknown", vector)
        lo, hi = decode(lower), decode(upper)
        assert lo is not None and hi is not None and 0 <= lo <= hi
        assert lo * lo <= a <= hi * hi, ("sqrt enclosure", vector, lower, upper)
        if lo * lo != a:
            assert decode(neighbor(lower, True)) ** 2 > a
        if hi * hi != a:
            below = decode(neighbor(upper, False))
            assert below >= 0 and below * below < a
        return
    exact = (a + b if op == 0 else a - b if op == 1 else a * b if op == 2 else a / b)
    if abs(exact) > decode(MAX):
        assert not success, ("overflow accepted", vector)
        return
    assert success, ("finite unknown", vector)
    lo, hi = decode(lower), decode(upper)
    assert lo is not None and hi is not None and lo <= exact <= hi, (vector, lower, upper)
    if lo != exact:
        assert decode(neighbor(lower, True)) > exact
    if hi != exact:
        assert decode(neighbor(upper, False)) < exact


def vectors():
    positive = [0, 1, 2, 3, 0xFFFFFFFFFFFFF, 0x10000000000000,
                0x10000000000001, 0x3C90000000000000, 0x3CA0000000000000,
                0x3FE0000000000000, 0x3FEFFFFFFFFFFFFF, 0x3FF0000000000000,
                0x3FF0000000000001, 0x4000000000000000, 0x4008000000000000,
                0x5FEFFFFFFFFFFFFF, MAX, 0x7FF0000000000000,
                0x7FF8000000000000, 0x7FF0000000000001]
    boundary = positive + [v | SIGN for v in positive]
    result = [(op, a, b) for op in range(4) for a in boundary for b in boundary]
    result += [(4, a, 0) for a in boundary]
    rng = random.Random(0x474941)
    result += [(op, rng.getrandbits(64), rng.getrandbits(64) if op != 4 else 0)
               for op in range(5) for _ in range(200)]
    return result


def main():
    executable, output = sys.argv[1:]
    cases = vectors()
    proc = subprocess.run([executable], input="".join(f"{op} {a:016x} {b:016x}\n"
                           for op, a, b in cases), text=True, capture_output=True, check=True)
    Path(output).write_text(proc.stdout)
    rows = proc.stdout.splitlines()
    assert len(rows) == len(cases) * 8
    cache = {}
    for index, row in enumerate(rows):
        i, mode, seed, success, lower, upper, restored = row.split()
        i, mode, seed, success, restored = map(int, (i, mode, seed, success, restored))
        lower, upper = int(lower, 16), int(upper, 16)
        assert (i, mode, seed) == (index // 8, index % 8 // 2, index % 2)
        assert restored == 1
        triple = success, lower, upper
        if i not in cache:
            verify(cases[i], *triple)
            cache[i] = triple
        else:
            assert cache[i] == triple, ("ambient state changed output", i)
    anchors = {
        (2, 1, 0x3FE0000000000000): (1, 0, 1),
        (2, SIGN | 1, 0x3FE0000000000000): (1, SIGN | 1, SIGN),
        (3, 1, 0x4000000000000000): (1, 0, 1),
        (3, SIGN | 1, 0x4000000000000000): (1, SIGN | 1, SIGN),
        (4, 1, 0): (1, 0x1E60000000000000, 0x1E60000000000000),
        (4, SIGN, 0): (1, SIGN, SIGN),
        (0, 0x3FF0000000000000, 0xBC90000000000000):
            (1, 0x3FEFFFFFFFFFFFFF, 0x3FF0000000000000),
        (0, 0x3FF0000000000000, 0xBFF0000000000000): (1, SIGN, 0),
    }
    lookup = {v: cache[i] for i, v in enumerate(cases)}
    for v, expected in anchors.items():
        assert lookup[v] == expected, ("bit anchor", v, lookup[v], expected)
    print(f"PASS: {len(cases)} exact-oracle vectors, {len(rows)} native calls, "
          f"4 incoming modes, 2 flag seeds, {len(anchors)} signed-bit anchors")


if __name__ == "__main__":
    main()
