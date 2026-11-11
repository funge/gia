"""Independent directed-operation and analytic oracles; not runtime arithmetic."""
from fractions import Fraction as Q
import math
import sys
from check_sine import decode, op, signed_point
from check_reduction import analytic as sin_bounds

PI = (Q(7074237752028440, 2**51), Q(7074237752028441, 2**51))
CELLS = [(-4, Q(-15,4), Q(-3,2), 'cos'),
         (Q(-15,4), Q(-9,4), -1, 'negSin'),
         (Q(-9,4), Q(-3,4), Q(-1,2), 'negCos'),
         (Q(-3,4), Q(3,4), 0, 'sin'),
         (Q(3,4), Q(9,4), Q(1,2), 'cos'),
         (Q(9,4), Q(15,4), 1, 'negSin'),
         (Q(15,4), 4, Q(3,2), 'negCos')]


def cosine(a):
    mul = lambda a, b: op(a, b, lambda x, y: x*y)
    div = lambda a, n: op(a, (Q(n), Q(n)), lambda x, y: x/y)
    x2 = mul(a, a)
    x4 = mul(x2, x2)
    x6 = mul(x4, x2)
    x8 = mul(x4, x4)
    p = op(op(op((Q(1), Q(1)), div(x2, 2), lambda x,y:x-y),
              div(x4, 24), lambda x,y:x+y), div(x6, 720), lambda x,y:x-y)
    r = op(p, (Q(0), div(x8, 40320)[1]), lambda x,y:x+y)
    return r[0], min(r[1], Q(1))


def cos_bounds(x):
    high = sum((-1)**k*x**(2*k)/math.factorial(2*k) for k in range(13))
    return high-x**26/math.factorial(26), high


def quadrants(a):
    outputs = []
    for l, u, c, mode in CELLS:
        j = (max(a[0], l), min(a[1], u))
        if j[1] < j[0]:
            continue
        shift = op((Q(c), Q(c)), PI, lambda x,y:x*y)
        residual = op(j, shift, lambda x,y:x-y)
        assert -1 <= residual[0] <= residual[1] <= 1
        if mode in ('sin', 'negSin'):
            r = (signed_point(residual[0])[0], signed_point(residual[1])[1])
        else:
            r = cosine(residual)
        if mode.startswith('neg'):
            r = op((Q(0), Q(0)), r, lambda x,y:x-y)
        outputs.append(r)
    assert outputs
    return min(r[0] for r in outputs), max(r[1] for r in outputs)


def check(path):
    counts = {'COSINE': 0, 'QUADRANTS': 0}
    saw_full = saw_peak = saw_trough = False
    for line in open(path):
        tag = line.split()[0] if line.split() else ''
        if tag not in counts:
            continue
        a, b, lo, hi = map(decode, line.split()[1:])
        assert -4 <= a <= b <= 4
        ref = cosine if tag == 'COSINE' else quadrants
        assert (lo, hi) == ref((a, b)), (tag, a, b)
        for k in range(17):
            x = a+(b-a)*Q(k, 16)
            low, high = (cos_bounds if tag == 'COSINE' else sin_bounds)(x)
            assert lo <= low <= high <= hi, (tag, a, b, k)
        if tag == 'COSINE':
            assert hi <= 1
            if a <= 0 <= b:
                assert hi == 1
        else:
            if a == -4 and b == 4:
                assert (lo, hi) == (-1, 1)
                saw_full = True
            if a == PI[0]/2 and b == PI[1]/2:
                assert hi == 1
                saw_peak = True
            if a == -PI[1]/2 and b == -PI[0]/2:
                assert lo == -1
                saw_trough = True
        counts[tag] += 1
    assert counts == {'COSINE': 68, 'QUADRANTS': 149}, counts
    assert saw_full and saw_peak and saw_trough
    print('PASS 68 cosine and 149 quadrant vectors: directed oracle and 17 analytic samples each')
    print('PASS whole [-4,4] result [-1,1], both extrema, shared boundaries and adjacent floats')


if __name__ == '__main__':
    check(sys.argv[1])
