"""Independent exact arithmetic oracle and descriptive native timing summary.
No hardware/runtime rational path and no performance pass/fail threshold.
"""
from fractions import Fraction as Q
import statistics
import sys
from check_sine import decode, op

X=('x',)
def C(q): return ('c',q)
one=C(Q(1)); huge=C(decode(0x7fefffffffffffff))
bubble=('m',X,('s',one,X))
exprs=[bubble,('m',X,X),('s',X,X),('m',bubble,('a',one,X)),
       ('m',('a',X,one),('s',X,one)),('m',X,C(Q(0))),
       ('s',('m',X,X),('m',X,X)),('a',X,C(Q(1,2**53))),
       ('m',huge,huge),('m',('s',X,X),huge),C(None)]
functions={'a':lambda x,y:x+y,'s':lambda x,y:x-y,'m':lambda x,y:x*y}
def interval(kind,a,b): return op(a,b,functions[kind])
def product(a,b):
    p0,p1=interval('m',a[:2],b[:2]),interval('m',a[2:],b[2:])
    d,e=interval('s',a[2:],a[:2]),interval('s',b[2:],b[:2])
    residual=interval('m',interval('m',d,e),(Q(0),Q(1,4)))
    return (*interval('s',p0,residual),*interval('s',p1,residual))
def evaluate(e,x,affine=False):
    if e[0]=='x': return (x[0],x[0],x[1],x[1]) if affine else x
    if e[0]=='c': return None if e[1] is None else (e[1],)*(4 if affine else 2)
    a,b=evaluate(e[1],x,affine),evaluate(e[2],x,affine)
    if a is None or b is None: return None
    try:
        if not affine: return interval(e[0],a,b)
        if e[0]=='m': return product(a,b)
        return (*interval(e[0],a[:2],b[:2]),*interval(e[0],a[2:],b[2:]))
    except (OverflowError,ValueError): return None

def value(e,x):
    if e[0]=='x': return x
    if e[0]=='c': return e[1]
    return functions[e[0]](value(e[1],x),value(e[2],x))
def parse(s):
    return s if s in ('none','unknown','conflict') else tuple(map(decode,s.split(':')))
def hull(a): return None if a is None else (min(a[0],a[2]),max(a[1],a[3]))
count=0; modes={'ordinary_only':0,'affine_only':0,'both':0,'unknown':0}; times={}
for line in open(sys.argv[1]):
    if line.startswith('DUAL_TIME '):
        _,i,trial,n,p,d=line.split(); assert int(n)==1000
        times.setdefault(int(i),[]).append((int(p)/int(n),int(d)/int(n)))
    if not line.startswith('DUAL '): continue
    _,i,l,u,o,a,r=line.split(); i=int(i); x=(decode(l),decode(u))
    ordinary=evaluate(exprs[i],x); affine=hull(evaluate(exprs[i],x,True))
    assert parse(o)==('none' if ordinary is None else ordinary),(i,x,o,ordinary)
    assert parse(a)==('none' if affine is None else affine),(i,x,a,affine)
    if ordinary is None and affine is None:
        expected='unknown'; modes['unknown']+=1
    elif ordinary is None:
        expected=affine; modes['affine_only']+=1
    elif affine is None:
        expected=ordinary; modes['ordinary_only']+=1
    else:
        expected=(max(ordinary[0],affine[0]),min(ordinary[1],affine[1])); modes['both']+=1
        assert expected[0]<=expected[1]
    actual=parse(r); assert actual==expected,(i,x,actual,expected)
    if isinstance(actual,tuple):
        if ordinary: assert ordinary[0]<=actual[0]<=actual[1]<=ordinary[1]
        for t in map(lambda n:Q(n,8),range(9)):
            v=value(exprs[i],(1-t)*x[0]+t*x[1])
            assert actual[0]<=v<=actual[1],(i,x,t,v,actual)
    if x==(0,1) and i in (0,1,2,3,4,6):
        width=lambda p: float(p[1]-p[0])
        print(f'DUAL_WIDTH expression {i}: ordinary={width(ordinary):.9g}, affine={width(affine):.9g}, combined={width(actual):.9g}')
    count+=1
assert count==66 and all(modes.values()),(count,modes)
assert set(times)=={0,1,3} and all(len(v)==5 for v in times.values())
for i,v in sorted(times.items()):
    p,d=statistics.median(x[0] for x in v),statistics.median(x[1] for x in v)
    print(f'DUAL_TIMING expression {i}: ordinary median {p:.1f} ns/eval; combined {d:.1f} ns/eval; ratio {d/p:.3f}; five paired trials')
print(f'PASS {count} dual evaluator cases, exact directed simulation and 9 real samples per successful result; {modes}')
