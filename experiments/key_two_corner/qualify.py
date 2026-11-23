#!/usr/bin/env python3
"""Exact Fraction corner oracle, separate from compiled Lean validation."""
import json, struct, subprocess
from fractions import Fraction as Q
from pathlib import Path

def bits(x): return struct.unpack('>Q',struct.pack('>d',x))[0]
def val(w): return Q.from_float(struct.unpack('>d',struct.pack('>Q',w))[0])
def case(a,b,c,d): return tuple(map(bits,(a,b,c,d)))
cases=[]
def add(name,ws,invalid=False): cases.append((name,ws,invalid))
base=case(-2,3,1,2)
for k in range(4):
 for w in [0x7ff0000000000000,0xfff0000000000000,0x7ff8000000000001,0x7ff0000000000001]:
  ws=list(base);ws[k]=w;add(f'invalid-{k}-{w:x}',ws,True)
for name,ws in [('reverse-num',case(3,-2,1,2)),('reverse-den',case(-2,3,2,1)),('cross',case(-2,3,-1,1)),('touch-neg',case(-2,3,-1,0)),('touch-pos',case(-2,3,-0.,1)),('zeros',case(-2,3,-0.,0.))]:add(name,ws,True)
for a,b in [(1,2),(-2,-1),(-2,3),(0,0),(0,2),(-2,0)]:
 for c,d in [(1,2),(2,2),(-2,-1),(-2,-2)]: add(f'row-{a}-{b}-{c}-{d}',case(a,b,c,d))
add('signed-zero',case(-0.,0.,-2,-1))
add('negative-minsub',(0x8000000000000001,0, bits(-4),bits(-2)))
add('positive-minsub',(1,2,bits(2),bits(4)))
add('overflow',(0x7fefffffffffffff,0x7fefffffffffffff,bits(.5),bits(1)))
add('finite-extreme',(0xffefffffffffffff,0x7fefffffffffffff,bits(1),bits(2)))
# Deterministic dyadic grid, both signs and non-singleton apertures.
for a in range(-4,5):
 for b in range(a,5):
  for c,d in [(1,3),(2,2),(-3,-1)]: add(f'grid-{a}-{b}-{c}-{d}',case(a/4,b/4,c/4,d/4))
add('negative-zero-lower',case(-0.,1.,2.,4.))
add('negative-zero-priority',case(-0.,-0.,2.,4.))
add('reversed-zero-bits',case(0.,-0.,2.,4.))
add('reversed-subnormal',(2,1,bits(2),bits(4)),True)
add('normal-boundary',(0x000fffffffffffff,0x0010000000000000,bits(2),bits(4)))
add('negative-normal-boundary',(0x8010000000000000,0x800fffffffffffff,bits(-4),bits(-2)))
add('adjacent-binade',(0x3fffffffffffffff,0x4000000000000000,bits(2),bits(4)))
cases=[(f'{name}@{rep}',w,invalid) for name,w,invalid in cases for rep in range(8)]
exe=Path('.lake/build/bin/keyCornerExperiment')
r=subprocess.run([str(exe.resolve())],input=''.join(' '.join(map(str,w))+'\n' for _,w,_ in cases),text=True,capture_output=True)
Path('experiments/key_two_corner/out/route-stdout.txt').write_text(r.stdout)
Path('experiments/key_two_corner/out/route-stderr.txt').write_text(r.stderr)
r.check_returncode()
lines=r.stdout.splitlines();assert len(lines)==len(cases),(r.stdout,r.stderr)
records=[];diff=availability=success=0
for (name,ws,invalid),line in zip(cases,lines):
 new,n,old,m,old_env,bridge,key,k,plan=[x.strip() for x in line.split('|')];n=int(n);m=int(m)
 def parse(s):return None if s=='none' else tuple(map(int,s.split()))
 new,old=parse(new),parse(old)
 key,k,plan=parse(key),int(k),parse(plan)
 assert key==new and k==n,(name,line)
 actual=tuple(map(int,bridge.split()))
 for expected,observed in zip(ws,actual):
  if expected != observed:
   # Only payload/signaling canonicalization is permitted. Never finite/zero changes.
   assert expected>>52&2047==observed>>52&2047==2047
   assert expected&((1<<52)-1) and observed&((1<<52)-1)

 if invalid:assert new is None and n==0 and plan is None,(name,line)
 else:
  assert old_env == "true",(name,line)
  assert n in (1,2) and m==4,(name,line)
  a,b,c,d=map(val,ws)
  if c>0:
   expected=(ws[0],ws[3],ws[1],ws[2]) if a>=0 else ((ws[0],ws[2],ws[1],ws[3]) if b<=0 else (ws[0],ws[2],ws[1],ws[2]))
  else:
   expected=(ws[1],ws[3],ws[0],ws[2]) if a>=0 else ((ws[1],ws[2],ws[0],ws[3]) if b<=0 else (ws[1],ws[3],ws[0],ws[3]))
  assert plan==expected,(name,line,expected)
  quot=[val(x)/val(y) for x in ws[:2] for y in ws[2:]]
  for o in (new,old):
   if o is not None: assert val(o[0])<=min(quot)<=max(quot)<=val(o[1]),(name,line)
  if old is not None:
   assert new is not None and val(old[0])<=val(new[0])<=val(new[1])<=val(old[1]),(name,line)
  success+=new is not None
  diff+=new is not None and old is not None and new!=old
  availability+=(new is None)!=(old is None)
 records.append(dict(name=name,words=ws,observed_words=actual,new=new,old=old,new_calls=n,old_calls=m,key=key,key_calls=k,requests=plan,invalid=invalid,old_environment_preserved=old_env))
Path('experiments/key_two_corner/out/qualification.json').write_text(json.dumps(records,indent=2)+'\n')
print(json.dumps(dict(cases=len(cases),invalid=sum(i for _,_,i in cases),success=success,raw_differences=diff,availability_differences=availability)))
for rec in records:
 if rec['name'] in ['signed-zero@0','negative-minsub@0','overflow@0']:print(json.dumps(rec))
# Separate compiled kernel qualification, completed before the benchmark is invoked.
import mpmath as mp
mp.mp.dps=100
r=subprocess.run([str(exe.resolve()),'kernels'],text=True,capture_output=True,check=True)
Path('experiments/key_two_corner/out/kernels.txt').write_text(r.stdout)
raw_diffs=0
assert len(r.stdout.splitlines()) == 45
for line in r.stdout.splitlines():
 left,reference,right=line.split('|');_,kind,i,*new=left.split();kind,i=int(kind),int(i)
 new=tuple(map(int,new));old=tuple(map(int,right.split()))
 assert new==tuple(map(int,reference.split()))
 assert len(new)==len(old)==2
 assert val(old[0])<=val(new[0])<=val(new[1])<=val(old[1])
 raw_diffs+=new!=old
 if kind in (2,3):
  x=mp.mpf(i%9+1)/16
  lo=x if kind==2 else -x
  hi=x+mp.mpf(1)/8
  lower=mp.mpf(val(new[0]).numerator)/val(new[0]).denominator
  upper=mp.mpf(val(new[1]).numerator)/val(new[1]).denominator
  fn=mp.sin if kind==2 else mp.cos
  for k in range(33): assert lower<=fn(lo+(hi-lo)*k/32)<=upper
print(json.dumps(dict(kernel_outputs=45,kernel_raw_differences=raw_diffs,transcendental_sample_precision_digits=100)))
