# Two-corner division: exact extrema and a conditional assembly bridge

[TwoCornerDivision.lean](TwoCornerDivision.lean) is a portable proof-side result.
It does not change the four-call hardware implementation, ASTs, renderer, or
rounding assumptions. It is independent of the affine-conjunction milestone.

## Ordered real intervals, with a strict denominator guard

For `a≤b`, `c≤d`, and either `0<c` or `d<0`, the selected corners are:

| Numerator | Denominator | Lower corner | Upper corner |
| --- | --- | --- | --- |
| `0≤a` | `0<c` | `a/d` | `b/c` |
| `b≤0` | `0<c` | `a/c` | `b/d` |
| `a≤0≤b` | `0<c` | `a/c` | `b/c` |
| `0≤a` | `d<0` | `b/d` | `a/c` |
| `b≤0` | `d<0` | `b/c` | `a/d` |
| `a≤0≤b` | `d<0` | `b/d` | `a/d` |

The real selector checks interval ordering, tests the denominator sign, then
selects the nonnegative numerator row first, the nonpositive row second, and the
straddling row otherwise. The boundary rows agree on values at zero. Singleton
numerators/denominators are allowed. These are finite real values: there are no
infinities or NaNs in this mathematical selector. It is `noncomputable` proof-side
Lean code, not an executable binary64 selector.

`select_spec` proves the selected operand pairs are interval corners and their
quotients enclose **every** independent pair of input values. `extrema_attained`
provides actual corner witnesses with nonzero denominators. `four_corner_extrema`
proves equality with the exact real min/max of all four corners, reusing the
existing `HardwareDivision.four_quotients` theorem. Attainment here is for the full
Cartesian product of the two intervals. For correlated expressions or externally
restricted domains, enclosure still applies to each actual pair, but those corner
witnesses need not be reachable. No exact-image assertion for such expressions is
made, and membership alone does not prove an actual value occurs.

The selector returns `none` for reversed intervals or any denominator interval
meeting zero, including one-sided touching and singleton zero. This is an absent
certificate, not a proof that all quotients are undefined. Crossing-zero split
semantics remain in [SplitQuotient](SPLIT_QUOTIENT.md); this change does not replace
them or discard their defined values.

## Conditional bridge, not a runtime optimization

`available_from_guard` uses the existing `CompareSound`, decoded zero and
`awayZero_sound`. **All four endpoints must decode to finite reals, and both
interval orders must be proved.** The strict scalar comparison guard alone does
not establish interval order. Scalar `CallSound` likewise only concerns its two
operands; it cannot validate an interval container. The fixture proves that two
representations decoding to real zero cannot pass the guard, covering the
intended signed-zero interpretation without asserting native bit decoding.

`assemble_selected_encloses` uses the existing division `CallSound` for the two
selected calls and the existing `HardwareAddition.assemble` defined in
[HardwareBounds.lean](HardwareBounds.lean). Successful assembly encloses the actual
quotient and proves its denominator nonzero. Operands must decode to the selected
real corners. This does not implement or verify a native sign selector. The
calls return **paired lower/upper bounds**: two paired-bound calls, not two single
rounding instructions. The unused side of each selected pair remains covered by
its full call contract; failure of either selected pair returns `none`.

The contract says successful calls enclose their exact values; it does not demand
correct rounding, minimal width, availability, or equality between implementations.
Consequently skipping two calls need not preserve the old four-call result:

- For `I=J=[1,2]`, the selected pairs are `(1,2)` and `(2,1)`. The omitted pairs
  are `(1,1)` and `(2,2)`; `(1,2)` is **not** an omitted corner in this example.
- An omitted `(1,1)` call may return `none` while still satisfying `CallSound`.
  Four-call assembly then fails, whereas the two selected exact pairs assemble
  `[1/2,2]`.
- An omitted `(1,1)` call may return the sound loose pair `[-10,10]`. With the
  other corners exact, four-call assembly returns `[-10,10]` while two-call
  assembly returns `[1/2,2]`.

These are kernel-checked contract models, not claims that the current native
adapter behaves that way. They rule out an unconditional availability/width
identity theorem from `CallSound` alone. This is distinct from
[directed scheduling](DIRECTED_SCHEDULING.md), which preserves all requests and
reassembles the same per-request outcomes. No batching, FP-state or performance
claim is made here.

## Source and implementation correspondence

The existing [hardware division account](HARDWARE_DIVISION.md) records the checked
Tupper sources: thesis §2.5.3 for directed arithmetic, §3.2.22 for division via
reciprocal/multiplication, and §3.2.26 for partial binary functions. This six-case
real monotonicity result is a derived optimization foundation for the existing
finite guarded theorem, not a claim to transcribe a particular Tupper chart.
The pinned relgraph C implementation and its reciprocal-then-multiply approach
are linked in that account; this change proves neither C correctness nor equal
rounded outputs. The existing adapter/compiler/hardware trust boundary is unchanged.

Run `lake build TwoCornerDivision`, `lake env lean tests/TwoCornerDivision.lean`,
and `./check.sh` with the pinned toolchain. [The fixture](tests/TwoCornerDivision.lean)
checks all six rows, attained corners, zero boundaries/numerator, singleton and
excluded denominators, reversed inputs, decoded zeros, the conditional assembly,
and the failure/width countermodels. See [qualification](VALIDATION.md).

A useful next question is whether a future native two-corner selector should
promise **sound enclosure only**, allowing improved availability/narrower output,
or preserve observable failure behavior of the four-call path. The latter needs
an explicit specification beyond the current enclosure contract; this milestone
adds no such assumption and makes no runtime change.
