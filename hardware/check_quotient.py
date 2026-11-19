"""Independent exact directed oracle for guarded quotient composition.
Undefined rational samples are rejected; division is never silently totalized.
"""
from fractions import Fraction as Q
from check_sine import decode, op
import sys
X=('x',)
C=lambda x:('c',x)
P=lambda p:('p',p)
B=lambda k,a,b:(k,a,b)
one,zero=P(C(Q(1))),P(C(Q(0)))
den=P(('s',C(Q(1,2)),('m',X,('s',C(Q(1)),X))))
safe=B('d',one,den)
exprs=[safe,B('d',one,P(('s',C(Q(1,2)),X))),B('d',one,B('s',zero,den)),
       B('a',safe,one),B('d',one,safe),B('s',safe,safe),B('m',safe,den),B('d',one,P(X)),
       B('d',zero,zero),B('d',P(C(decode(0x7fefffffffffffff))),P(C(decode(1)))),
       B('d',P(('m',X,C(Q(0)))),one),B('d',P(('s',X,X)),one)]
fs={'a':lambda x,y:x+y,'s':lambda x,y:x-y,'m':lambda x,y:x*y,'d':lambda x,y:x/y}
def interval(k,a,b):
    if a is None or b is None: return None
    if k=='d' and b[0]<=0<=b[1]: return None
    try: return op(a,b,fs[k])
    except (OverflowError,ValueError): return None

def polynomial(e,x,affine=False):
    if e[0]=='x': return (x[0],x[0],x[1],x[1]) if affine else x
    if e[0]=='c': return (e[1],)*(4 if affine else 2)
    a,b=polynomial(e[1],x,affine),polynomial(e[2],x,affine)
    if a is None or b is None: return None
    if not affine: return interval(e[0],a,b)
    if e[0]!='m':
        l,h=interval(e[0],a[:2],b[:2]),interval(e[0],a[2:],b[2:])
    else:
        p0,p1=interval('m',a[:2],b[:2]),interval('m',a[2:],b[2:])
        d,f=interval('s',a[2:],a[:2]),interval('s',b[2:],b[:2])
        r=interval('m',interval('m',d,f),(Q(0),Q(1,4)))
        l,h=interval('s',p0,r),interval('s',p1,r)
    return None if l is None or h is None else (*l,*h)

def merge(a,b):
    if a is None: return b
    if b is None: return a
    r=(max(a[0],b[0]),min(a[1],b[1])); assert r[0]<=r[1]
    return r

def evaluate(e,x):
    if e[0]=='p':
        o,a=polynomial(e[1],x),polynomial(e[1],x,True)
        return o,merge(o,None if a is None else (min(a[0],a[2]),max(a[1],a[3])))
    a,b=evaluate(e[1],x),evaluate(e[2],x)
    o,r=interval(e[0],a[0],b[0]),interval(e[0],a[1],b[1])
    return o,merge(o,r)

def val(e,x):
    if e[0]=='p': return val(e[1],x)
    if e[0]=='x': return x
    if e[0]=='c': return e[1]
    a,b=val(e[1],x),val(e[2],x)
    if a is None or b is None or (e[0]=='d' and b==0): return None
    return fs[e[0]](a,b)
def parse(s): return None if s in ('none','unknown') else tuple(map(decode,s.split(':')))
count=ordinary=refined=unknown=0
for line in open(sys.argv[1]):
    if not line.startswith('QUOTIENT '): continue
    _,i,l,u,o,r=line.split(); i=int(i); x=(decode(l),decode(u))
    expected=evaluate(exprs[i],x); got=(parse(o),parse(r)); assert got==expected,(i,x,got,expected)
    a,b=got
    if a is not None:
        ordinary+=1; assert b is not None and a[0]<=b[0]<=b[1]<=a[1]
    if b is not None:
        refined+=1
        for n in range(17):
            t=Q(n,16); v=val(exprs[i],(1-t)*x[0]+t*x[1])
            assert v is not None and b[0]<=v<=b[1],(i,x,t,v,b)
    else: unknown+=1
    if i==0 and x==(0,1): assert a is None and b==(2,4)
    if i==1 and x==(0,1):
        assert b is None and val(exprs[i],Q(0))==2 and val(exprs[i],Q(1,2)) is None
    if i==5 and x==(0,1): assert b==(-2,2) # no quotient cancellation claim
    count+=1
assert count==84 and ordinary and refined>ordinary and unknown
print(f'PASS {count} guarded quotient cases: {ordinary} ordinary successes preserved, {refined} refined successes, {unknown} unknown')
print('PASS independent strict-domain samples, [2,4] acceptance, genuine pole, and correlation-loss control [-2,2]')
