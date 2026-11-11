"""Exact reconstruction simulation and independent large-argument samples."""
from fractions import Fraction as Q
import sys
from check_sine import decode, op, signed_point
from check_quadrants import cosine, PI, CELLS
from check_split import reference as split
from check_dyadic import independent


def local(a, depth=3):
    if depth == 0:
        return (signed_point(a[0])[0],signed_point(a[1])[1]), cosine(a)
    half = op(a,(Q(2),Q(2)),lambda x,y:x/y)
    s,c = local(half,depth-1)
    ts = op((Q(2),Q(2)),s,lambda x,y:x*y)
    ss = op(ts,c,lambda x,y:x*y)
    cc = op(c,c,lambda x,y:x*y)
    tcc = op((Q(2),Q(2)),cc,lambda x,y:x*y)
    return ss,op(tcc,(Q(1),Q(1)),lambda x,y:x-y)


def fine_quadrants(a):
    outputs=[]
    for l,u,c,mode in CELLS:
        j=max(a[0],l),min(a[1],u)
        if j[1]<j[0]:continue
        shift=op((Q(c),Q(c)),PI,lambda x,y:x*y)
        residual=op(j,shift,lambda x,y:x-y)
        assert -1 <= residual[0] <= residual[1] <= 1
        ss,cc=local(residual)
        r=ss if mode in ('sin','negSin') else cc
        if mode.startswith('neg'):
            r=op((Q(0),Q(0)),r,lambda x,y:x-y)
        outputs.append(r)
    return min(r[0] for r in outputs),max(r[1] for r in outputs)


def fine_global(a):
    for c in (0,2,-2,4,-4):
        shift = op((Q(c),Q(c)),PI,lambda x,y:x*y)
        try:
            residual = op(a,shift,lambda x,y:x-y)
        except OverflowError:
            continue
        if -4 <= residual[0] <= residual[1] <= 4:
            return fine_quadrants(residual),True
    return (Q(-1),Q(1)),False


def check(path):
    count = improved = 0
    saw_large = saw_wide = False
    for line in open(path):
        if not line.startswith('FINE '):
            continue
        a,b,lo,hi,oldlo,oldhi = map(decode,line.split()[1:])
        old = split((a,b))
        raw = split((a,b),fine_global)
        expected = max(old[0],raw[0]),min(old[1],raw[1])
        assert (lo,hi) == expected and (oldlo,oldhi) == old
        assert oldlo <= lo <= hi <= oldhi
        if max(abs(a),abs(b)) <= 2**40+1:
            for k in range(9):
                low,high = independent(a+(b-a)*Q(k,8))
                assert lo <= low <= high <= hi, (a,b,k)
        else:
            assert (lo,hi) == (-1,1)
        if a == b and abs(a) <= 2**40 and hi-lo < oldhi-oldlo:
            improved += 1
        if a == b == 10**12:
            assert hi-lo < (oldhi-oldlo)/1000
            print('Observed 1e12 halved/previous widths:',float(hi-lo),float(oldhi-oldlo))
            saw_large = True
        if (a,b) == (Q(-3,4),Q(3,4)):
            assert raw[1]-raw[0] > oldhi-oldlo and (lo,hi) == old
            saw_wide = True
        count += 1
    assert count == 138 and improved > 50 and saw_large and saw_wide, (count,improved,saw_large,saw_wide)
    print(f'PASS {count} halving comparisons, {improved} strictly improved bounded points, no wider outputs')
    print('PASS independent analytic samples and wide-interval dependency control')


if __name__ == '__main__':
    check(sys.argv[1])
