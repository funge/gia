# compositional interval evaluator

This optional research milestone adds rational constants, `x`, `y`, addition,
subtraction, multiplication, and guarded division. It does not change relgraph's
native build, release requirements, or hosted CI.

## semantics and result

`Value x y e z` is an inductive, partial real semantics. Its division rule requires
the denominator's value to be nonzero. There is no rule assigning a value to
division by zero; `division_by_zero_undefined` proves this for `1 / 0`.

`eval B X Y e` returns either `some R`, an interval, or `none`, meaning unknown.
Input boxes use the existing finite, ordered rational intervals interpreted over
the reals. Variable leaves use those supplied boxes; constants and operation
results go through backend `B`.

The central theorem `eval_sound` proves:

```text
BackendSound B
X.Contains x
Y.Contains y
Value x y e z
eval B X Y e = some R
--------------------------------
R.Contains z
```

It is proved by induction on the partial evaluation derivation. It covers every
defined point, including nonrepresentable real points between the endpoints.
`eval_empty_pixel` then proves that an `empty` classification rules out every
defined zero of the expression in the box. It does not invent values at undefined
points or assert that an unresolved box contains a root.

## exact backend

`exactBackend` returns the exact rational primitive bounds, with no rounding:

- constants: singleton intervals;
- addition and subtraction: the existing endpoint formulas;
- multiplication: the minimum and maximum of all four endpoint products;
- division: multiply by `[1/hi, 1/lo]` only if `hi < 0` or `0 < lo`.

The reciprocal proof covers positive and negative denominators. If zero is in
the denominator interval, including either endpoint, division returns unknown.
`guardedDiv_denominator_nonzero` proves that successful guarded division has a
nonzero denominator at every point enclosed by that denominator interval.

These are exact arithmetic bounds, not a claim of tight bounds for compound
expressions. Repeated occurrences of a variable lose dependency information.

## shared directed-rounding backend

The same `eval_sound` theorem supports `directedBackend down up`. It widens each
exact primitive result with optional finite endpoint conversions. The contracts
are the same outward inequalities as in the previous milestone, required only
when a conversion succeeds:

```text
down q = some r  →  r ≤ q
up   q = some r  →  q ≤ r
```

`directedBackend_sound` proves the backend enclosure contract from these two
assumptions. `eval_directed_sound` and `directed_empty_pixel` specialize the common
results. A failed conversion returns unknown; no total finite-output assumption
is made. The adapter also rejects reversed output endpoints. Rounded denominator
intervals are checked for zero before division, so widening may conservatively
turn a formerly decidable division into unknown.

The reference remains [IEEE 754-2019](https://standards.ieee.org/ieee/754/6210/),
with downward and upward directions interpreted as toward negative and positive
infinity. The intended application is binary64, but the theorem is independent
of format and does not encode representability. No extra FP assumptions were
introduced: the successful endpoint inequalities remain explicit hypotheses.
No actual IEEE rounding algorithm, per-instruction C operation, exception flag,
overflow/underflow policy, NaN, infinity, signed-zero behavior, or FP environment
is verified. Finite subnormal values can be represented as rationals, but their
rounding behavior is not independently established here.

The adapter rounds the exact primitive interval bounds. Equivalence to a concrete
implementation that rounds intermediate products or reciprocals requires a
separate implementation proof; it is not asserted by this evaluator.

## checked examples

`EvaluatorExamples.lean` includes proof-checked examples:

| expression / condition | result |
| --- | --- |
| `(x*x - 1)/(y + 2)`, `x ∈ [2,3]`, `y ∈ [0,1]` | `[1,4]`, empty for equality to zero; no-root corollary |
| `x/y`, `x ∈ [3,8]`, `y ∈ [-3,-2]` | `[-4,-1]` |
| `x*y`, `x ∈ [-2,3]`, `y ∈ [-4,5]` | `[-12,15]` |
| denominator interval `[-1,1]` or `[0,1]` | unknown |
| `1/x` on `x ∈ [-1,1]` | unknown, despite a proved defined value at `x=1` |
| `1/(x*x+1)` on `x ∈ [-1,1]` | unknown from dependency loss; separately proved defined for every real `x,y` |
| `1/0` | no real semantic value |
| synthetic widening by one in each direction | enclosure contracts proved; widening a denominator `[1,1]` to `[0,2]` makes division unknown |
| endpoint conversion failure | unknown |

The synthetic widening example is not an IEEE rounding implementation. Examples
use kernel-checked proof tactics, not `native_decide` or native floating-point
evaluation. `Audit.lean` covers the exported theorems and example proofs.

## files and validation

- `IntervalOps.lean`: multiplication, guarded reciprocal, and enclosure proofs.
- `Evaluator.lean`: syntax, partial semantics, evaluation, common soundness,
  division guard, and zero-exclusion result.
- `EvaluatorRounding.lean`: directed-rounding adapter and specialized theorems.
- `EvaluatorExamples.lean`: numerical and domain controls.

Run `lake build` and `lake env lean Audit.lean` from this directory with the pinned
toolchain. The default Lean build includes the evaluator and all examples.
See `VALIDATION.md` for observed results. The subsequent [presence milestone](PRESENCE.md)
derives definedness and continuity along curves from successful evaluation, and
uses certified endpoint signs to prove existence of a root. Subdivision,
optimality, performance, parser correctness, and implementation refinement
remain outside these results.
