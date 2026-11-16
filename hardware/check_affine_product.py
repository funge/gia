"""Test-only exact directed arithmetic and independent polynomial-extrema oracle.
The executable product uses the hardware adapter, never rational arithmetic.
"""
from fractions import Fraction as Q
from itertools import product
import sys
from check_sine import decode, op

sub = lambda a,b: op(a,b,lambda x,y:x-y)
mul = lambda a,b: op(a,b,lambda x,y:x*y)
def reference(a,b):
    p0,p1=mul(a[:2],b[:2]),mul(a[2:],b[2:])
    curvature=mul(sub(a[2:],a[:2]),sub(b[2:],b[:2]))
    residual=mul(curvature,(Q(0),Q(1,4)))
    return (*sub(p0,residual),*sub(p1,residual))

def at(a,t):
    return ((1-t)*a[0]+t*a[2],(1-t)*a[1]+t*a[3])

def extrema(p,q,r):
    ts=[Q(0),Q(1)]
    if r and 0 < -q/(2*r) < 1:
        ts.append(-q/(2*r))
    return [p+q*t+r*t*t for t in ts]

count=better=worse=0
for line in open(sys.argv[1]):
    if not line.startswith('AFFINE_PRODUCT '): continue
    nums=list(map(decode,line.split()[1:])); assert len(nums)==20
    a,b,o,h,ordinary,chained=nums[:4],nums[4:8],nums[8:12],nums[12:14],nums[14:16],nums[16:]
    assert tuple(o)==reference(a,b)
    assert tuple(chained)==reference(o,(Q(1),Q(1),Q(2),Q(2)))
    assert h==[min(o[0],o[2]),max(o[1],o[3])]
    assert tuple(ordinary)==mul((min(a[0],a[2]),max(a[1],a[3])),(min(b[0],b[2]),max(b[1],b[3])))
    better+=h[1]-h[0]<ordinary[1]-ordinary[0]
    worse+=h[1]-h[0]>ordinary[1]-ordinary[0]
    # Exact extrema of each corner quadratic minus each output affine bound.
    # This checks all parameters, not only a sample grid, for all four
    # endpoint witnesses of each operand (16 combinations).
    for a0,a1,b0,b1 in product(a[:2],a[2:],b[:2],b[2:]):
        p=a0*b0; q=a0*(b1-b0)+b0*(a1-a0); r=(a1-a0)*(b1-b0)
        assert min(extrema(p-o[0],q-(o[2]-o[0]),r))>=0
        assert max(extrema(p-o[1],q-(o[3]-o[1]),r))<=0
        for t in (Q(0),Q(1,8),Q(1,2),Q(7,8),Q(1)):
            value=(p+q*t+r*t*t)*(1+t)
            lo,hi=at(chained,t)
            assert lo<=value<=hi
    if count==1: # t * (1-t), with both extremal values attained
        assert h==[0,Q(1,4)] and ordinary==[0,1]
    count+=1
assert count==64,count
assert better and worse, (better,worse)
print(f'PASS {count} affine products and compositions: exact directed oracle and continuous quadratic-extrema checks')
print(f'Affine versus ordinary hull widths: {better} tighter, {worse} wider, {count-better-worse} equal; no universal tightening claim')
