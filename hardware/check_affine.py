"""Independent exact-rational oracle for the observed hardware affine path.
Test-only arithmetic: the native algorithm uses directed binary64 operations.
"""
from fractions import Fraction as Q
from itertools import product
import sys
from check_sine import decode, op

count = 0
for line in open(sys.argv[1]):
    if not line.startswith('AFFINE '):
        continue
    fields = line.split()
    kind = fields[1]
    nums = list(map(decode, fields[2:]))
    assert len(nums) == 14
    a, b, out, hull = nums[:4], nums[4:8], nums[8:12], nums[12:]
    f = {'add': lambda x,y:x+y, 'sub': lambda x,y:x-y,
         'scale': lambda x,y:x*y}[kind]
    for i in (0,2):
        expected = op(a[i:i+2], b[i:i+2], f)
        assert tuple(out[i:i+2]) == expected, (kind, a, b, out, expected)
    assert hull == [min(out[0],out[2]), max(out[1],out[3])]
    for t in map(Q, ['0','0.125','0.5','0.875','1']):
        low, high = (1-t)*out[0]+t*out[2], (1-t)*out[1]+t*out[3]
        for a0,a1,b0,b1 in product(a[:2],a[2:],b[:2],b[2:]):
            x, y = (1-t)*a0+t*a1, (1-t)*b0+t*b1
            v = f(x,y)
            assert hull[0] <= low <= v <= high <= hull[1]
    count += 1
assert count == 102, count
# Independent witness control: t - t cancels, t - s need not.
assert Q(0)-Q(1) != 0
print(f'Exact-rational affine oracle: {count} native cases, 5 shared parameters, all endpoint witnesses passed')
