"""Independent exact-rational test oracle for observed binary64 sine bounds.
Not part of runtime, not a hardware verification, and never calls libm sin.
"""
from fractions import Fraction as Q
import math
import struct
import sys


def decode(bits):
    x = struct.unpack('>d', int(bits).to_bytes(8, 'big'))[0]
    assert math.isfinite(x)
    return Q(x)


def rounded(x, upward):
    v = float(x)
    if (Q(v) < x if upward else x < Q(v)):
        v = math.nextafter(v, math.inf if upward else -math.inf)
    return Q(v)


def op(a, b, f):
    vals = [f(x, y) for x in a for y in b]
    return rounded(min(vals), False), rounded(max(vals), True)


def reference(a):
    mul = lambda a, b: op(a, b, lambda x, y: x*y)
    div = lambda a, n: op(a, (Q(n), Q(n)), lambda x, y: x/y)
    x2 = mul(a, a)
    x3 = mul(x2, a)
    x5 = mul(x3, x2)
    x7 = mul(x5, x2)
    p = op(op(a, div(x3, 6), lambda x, y: x-y), div(x5, 120), lambda x, y: x+y)
    return op(p, (Q(0), div(x7, 5040)[1]), lambda x, y: x-y)


def signed_point(x):
    zero = (Q(0), Q(0))
    if x < 0:
        reflected = op(zero, (x, x), lambda a, b: a-b)
        return op(zero, reference(reflected), lambda a, b: a-b)
    return reference((x, x))


def analytic(x):
    t = abs(x)
    terms = [(-1)**k*t**(2*k+1)/math.factorial(2*k+1) for k in range(9)]
    high = sum(terms)
    low = high-t**19/math.factorial(19)
    return (-high, -low) if x < 0 else (low, high)


def check_endpoints(path):
    count = 0
    unit_width = None
    for line in open(path):
        if not line.startswith('SINE_ENDPOINTS '):
            continue
        a, b, lo, hi = map(decode, line.split()[1:])
        assert -1 <= a <= b <= 1
        assert (lo, hi) == (signed_point(a)[0], signed_point(b)[1]), (a, b, lo, hi)
        for k in range(9):
            low, high = analytic(a+(b-a)*Q(k, 8))
            assert lo <= low <= high <= hi, (a, b, k)
        if 0 <= a:
            old = reference((a, b))
            assert old[0] <= lo <= hi <= old[1], (a, b)
            if a == 0 and b == 1:
                assert hi-lo < old[1]-old[0]
                unit_width = (float(old[1]-old[0]), float(hi-lo))
        count += 1
    assert count == 73, count
    assert unit_width is not None
    print(f'PASS {count} signed endpoint vectors: directed oracle and 9 analytic samples each')
    print(f'Observed [0,1] widths: natural={unit_width[0]}, endpoints={unit_width[1]}')


def check(path):
    count = 0
    widths = {}
    for line in open(path):
        if not line.startswith('SINE '):
            continue
        a, b, lo, hi = map(decode, line.split()[1:])
        assert 0 <= a <= b <= 1
        assert (lo, hi) == reference((a, b)), (a, b, lo, hi)
        for x in (a, (a+b)/2, b):
            p = x - x**3/6 + x**5/120
            assert lo <= p-x**7/5040 <= p <= hi
            # A distinct higher-order alternating-series check, not the runtime polynomial.
            terms = [(-1)**k*x**(2*k+1)/math.factorial(2*k+1) for k in range(9)]
            high = sum(terms)
            low = high-x**19/math.factorial(19)
            assert lo <= low <= high <= hi
        if a == b and a in (0, Q(1, 2), 1):
            widths[str(a)] = float(hi-lo)
        count += 1
    assert count == 39, count
    print(f'PASS {count} sine vectors: exact directed-arithmetic and analytic enclosure oracles')
    print(f'Observed point widths (including rounding): {widths}')


if __name__ == '__main__':
    check(sys.argv[1])
    check_endpoints(sys.argv[1])
