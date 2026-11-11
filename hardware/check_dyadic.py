"""Exact directed simulation plus independent high-precision Machin reduction."""
from fractions import Fraction as Q
import sys
from check_sine import decode, op
from check_quadrants import PI
from check_global import reference as local_reference
from check_reduction import pi_bounds, analytic


def reference(a, levels=20):
    for sign in (1,-1):
        for k in reversed(range(levels)):
            c = Q(sign*2**(k+1))
            shift = op((c,c), PI, lambda x,y:x*y)
            accept = ((shift[0] >= 0 and a[0] >= shift[1]) or
                      (shift[1] <= 0 and a[1] <= shift[0]))
            if accept:
                try:
                    a = op(a,shift,lambda x,y:x-y)
                except OverflowError:
                    return (Q(-1),Q(1))
    return local_reference(a)[0]


PL, PU = pi_bounds()
# Outward dyadic compression keeps the exact oracle fast without losing its
# independently derived Machin containment; it remains far tighter than binary64.
DEN = 2**160
PL = Q((PL*DEN)//1,DEN)
PU = Q(-((-PU*DEN)//1),DEN)


def independent(x):
    # This quotient is test-only exact rational arithmetic, not the runtime
    # shift selection. Machin pi is independent of the runtime binary64 bracket.
    n = (x/(PL+PU)+Q(1,2)) // 1
    center = x-n*(PL+PU)
    radius = abs(n)*(PU-PL)
    lo,hi = analytic(center)
    # |sin(a)-sin(b)| <= |a-b| bounds uncertainty in the independent reduction.
    return lo-radius,hi+radius


def check(path):
    count = useful = 0
    for line in open(path):
        if not line.startswith('DYADIC '):
            continue
        a,b,lo,hi = map(decode,line.split()[1:])
        assert (lo,hi) == reference((a,b)), (a,b,lo,hi)
        if max(abs(a),abs(b)) <= 1048576+1:
            for k in range(9):
                low,high = independent(a+(b-a)*Q(k,8))
                assert lo <= low <= high <= hi, (a,b,k)
            if b-a <= Q(1,4):
                assert hi-lo < Q(1,2), (a,b,hi-lo)
                useful += 1
        else:
            assert (lo,hi) == (-1,1)
        count += 1
    assert count == 138 and useful == 134, (count,useful)
    print(f'PASS {count} dyadic vectors, {useful} narrow refinements, independent Machin/series oracle')


if __name__ == '__main__':
    check(sys.argv[1])
