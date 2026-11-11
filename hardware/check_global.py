"""Independent finite search simulation; global bounds do not need a huge-angle oracle."""
from fractions import Fraction as Q
import sys
import math
from check_sine import decode, op
from check_quadrants import PI, quadrants
def analytic(x):
    t = abs(x)
    assert t <= 16
    high = sum((-1)**k*t**(2*k+1)/math.factorial(2*k+1) for k in range(61))
    low = high-t**123/math.factorial(123)
    return (-high,-low) if x < 0 else (low,high)



def reference(a):
    for c in (0, 2, -2, 4, -4):
        shift = op((Q(c), Q(c)), PI, lambda x, y: x*y)
        try:
            residual = op(a, shift, lambda x, y: x-y)
        except OverflowError:
            # A directed endpoint is nonfinite: the native adapter rejects it.
            continue
        if -4 <= residual[0] <= residual[1] <= 4:
            return quadrants(residual), True
    return (Q(-1), Q(1)), False


def check(path):
    total = refined = fallback = 0
    shifted_peak = negative_peak = False
    for line in open(path):
        if not line.startswith('GLOBAL '):
            continue
        a, b, lo, hi = map(decode, line.split()[1:])
        expected, used = reference((a, b))
        assert (lo, hi) == expected, (a, b, lo, hi, expected)
        if max(abs(a), abs(b)) <= 16:
            for k in range(9):
                low, high = analytic(a + (b-a)*Q(k, 8))
                assert lo <= low <= high <= hi, (a,b,k)
        else:
            assert not used and (lo,hi) == (-1,1)
        if (a,b) == (Q(15,2),Q(8)):
            assert used and lo > 0 and hi == 1
            shifted_peak = True
        if (a,b) == (Q(-8),Q(-15,2)):
            assert used and lo == -1 and hi < 0
            negative_peak = True
        refined += used
        fallback += not used
        total += 1
    assert total == 267 and refined > 0 and fallback > 0
    assert shifted_peak and negative_peak
    print(f'PASS {total} global sine vectors: {refined} reduced, {fallback} global fallback')
    print('PASS independent shifted-extremum controls and maximum-finite fallback')


if __name__ == '__main__':
    check(sys.argv[1])
