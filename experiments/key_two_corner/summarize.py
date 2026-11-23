#!/usr/bin/env python3
import json,statistics,sys
from collections import defaultdict
rows=defaultdict(list); outputs=0; calls_total=defaultdict(int)
for line in open(sys.argv[1]):
 if line.startswith('BENCH '):
  _,kind,mode,n,good,calls,ns,digest=line.split()
  n,good,calls,ns=map(int,(n,good,calls,ns));assert n==good
  expected={'0':4,'1':4,'2':12,'3':16,'4':4}[kind]*n
  if mode!='0':expected//=2
  assert calls==expected
  if n==2000:
   rows['end-to-end',kind,mode].append(ns/n);outputs+=good;calls_total[mode]+=calls
 elif line.startswith('SELECT '):
  _,mode,n,good,ns,digest=line.split();n,good,ns=map(int,(n,good,ns))
  assert good==n*3//4
  if n==2000:rows['selector','mixed-valid-invalid',mode].append(ns/n)
assert set(rows) == {('end-to-end',str(k),str(m)) for k in range(5) for m in range(3)} | {('selector','mixed-valid-invalid',str(m)) for m in (1,2)}
for key,vs in rows.items():
 assert len(vs)==(10 if key[0]=='selector' else 9)
 print(json.dumps(dict(scope=key[0],kind=key[1],mode=key[2],ns_median=statistics.median(vs),ns_range=[min(vs),max(vs)])))
print(json.dumps(dict(measured_outputs=outputs,paired_calls=dict(calls_total))))
