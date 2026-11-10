"""Independent finite-vector oracle: exact binary arithmetic and Machin pi bounds.
Test-only rational arithmetic; the runtime uses hardware binary64 primitives.
"""
from fractions import Fraction as Q
import math
import sys
from check_sine import decode, op, signed_point


def atan_bounds(x, n=40):
    # Even last index gives an upper alternating partial sum for 0 < x < 1.
    high = sum((-1)**k*x**(2*k+1)/(2*k+1) for k in range(n+1))
    return high-x**(2*n+3)/(2*n+3), high


def pi_bounds():
    a, b = atan_bounds(Q(1, 5))
    c, d = atan_bounds(Q(1, 239))
    return 16*a-4*d, 16*b-4*c


def reference(a, pi):
    for c in (0, 2, -2, 4, -4):
        shift = op((Q(c), Q(c)), pi, lambda x, y: x*y)
        residual = op(a, shift, lambda x, y: x-y)
        if -1 <= residual[0] <= residual[1] <= 1:
            return signed_point(residual[0])[0], signed_point(residual[1])[1]
    return None


def analytic(x):
    # For |x| <= 14 the tail after index 40 is decreasing. This series is
    # evaluated at the ORIGINAL input, independently of pi and range reduction.
    t = abs(x)
    assert t <= 14
    high = sum((-1)**k*t**(2*k+1)/math.factorial(2*k+1) for k in range(41))
    low = high-t**83/math.factorial(83)
    return (-high, -low) if x < 0 else (low, high)


def check(path):
    lines = open(path).readlines()
    pi_lines = [line for line in lines if line.startswith('PI_BOUNDS ')]
    assert len(pi_lines) == 1
    pi = tuple(map(decode, pi_lines[0].split()[1:]))
    assert pi == (Q(7074237752028440, 2251799813685248),
                  Q(7074237752028441, 2251799813685248))
    lower, upper = pi_bounds()
    assert pi[0] < lower < upper < pi[1]
    assert pi[1]-pi[0] == Q(1, 2**51)
    count = 0
    for line in lines:
        if not line.startswith('SINE_REDUCED '):
            continue
        a, b, lo, hi = map(decode, line.split()[1:])
        assert (lo, hi) == reference((a, b), pi), (a, b)
        for k in range(9):
            low, high = analytic(a+(b-a)*Q(k, 8))
            assert lo <= low <= high <= hi, (a, b, k)
        count += 1
    assert count == 92, count
    for a in ((Q(3, 2), Q(3, 2)), (Q(0), Q(7)), (Q(100), Q(100))):
        assert reference(a, pi) is None
    print('PASS pi bit patterns and containment against independent Machin bounds')
    print(f'PASS {count} reduced sine vectors: exact hardware simulation and original-input series')


if __name__ == '__main__':
    check(sys.argv[1])
