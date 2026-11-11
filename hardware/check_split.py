"""Split arithmetic simulation and independent Machin/series validation."""
from fractions import Fraction as Q
import sys
from check_sine import decode, op
from check_quadrants import PI
from check_global import reference as local_reference
from check_dyadic import reference as unsplit, independent, PL, PU

H = PI[0]
T = (Q(2483825185828341,2**104),Q(1242014004962189,2**103))


def reference(a):
    low = (Q(0),Q(0))
    for sign in (1,-1):
        for k in reversed(range(40)):
            c = Q(sign*2**(k+1))
            shift = op((c,c),(H,H),lambda x,y:x*y)
            accept = ((shift[0] >= 0 and a[0] >= shift[1]) or
                      (shift[1] <= 0 and a[1] <= shift[0]))
            if accept:
                try:
                    a = op(a,shift,lambda x,y:x-y)
                    correction = op((c,c),T,lambda x,y:x*y)
                    low = op(low,correction,lambda x,y:x+y)
                except OverflowError:
                    return Q(-1),Q(1)
    try:
        residual = op(a,low,lambda x,y:x-y)
    except OverflowError:
        return Q(-1),Q(1)
    return local_reference(residual)[0]


def check(path):
    count = useful = 0
    saw_tail = saw_improvement = False
    for line in open(path):
        if line.startswith('PI_TAIL '):
            assert tuple(map(decode,line.split()[1:])) == T
            assert H+T[0] < PL < PU < H+T[1]
            assert T[1]-T[0] < (PI[1]-PI[0])/40000
            saw_tail = True
        if not line.startswith('SPLIT '):
            continue
        a,b,lo,hi,oldlo,oldhi = map(decode,line.split()[1:])
        assert (lo,hi) == reference((a,b)), (a,b)
        assert (oldlo,oldhi) == unsplit((a,b),40), (a,b)
        if max(abs(a),abs(b)) <= 2**40+1:
            for k in range(9):
                low,high = independent(a+(b-a)*Q(k,8))
                assert lo <= low <= high <= hi, (a,b,k)
            if b-a <= Q(1,4):
                assert hi-lo < Q(1,2), (a,b,hi-lo)
                useful += 1
        else:
            assert (lo,hi) == (-1,1)
        if a == b == 10**12:
            assert hi-lo < (oldhi-oldlo)/2
            print('Observed 1e12 widths:',float(hi-lo),float(oldhi-oldlo))
            saw_improvement = True
        count += 1
    assert count == 138 and useful == 134, (count,useful)
    assert saw_tail and saw_improvement
    print('PASS split constants against independent Machin pi; 138 split/unsplit comparisons')
    print('PASS 134 narrow refinements and independent large-argument analytic samples')


if __name__ == '__main__':
    check(sys.argv[1])
