# Directed hardware interval square root

[HardwareSquareRoot.lean](HardwareSquareRoot.lean) extends the finite hardware
path with a conditional proof for nonnegative and mixed-domain intervals. The
[compiled Lean client](hardware/Main.lean) calls native binary64 square root in
downward and upward rounding modes, then uses the same `assemble` endpoint
selection as the proof. It does not compute rational approximations at runtime.

## Proved mathematics and partiality

For input endpoints `a,b` and a represented value `x ≥ 0`, the lower call is on
`max(a,0)` and the upper call is on `b`. Monotonicity of real square root proves
that their outward-rounded results enclose `sqrt(x)`. The theorem assumes finite
max selection agrees with real max, zero decodes to real zero, and the two observed
primitive calls enclose their nonnegative inputs' roots. These are explicit
hypotheses, not new axioms. The max/zero representation boundary is the one already
used for hardware arithmetic; square root is an IEEE directed primitive covered
by the approved rounding assumption.

`assemble_sqrtValues` connects successful hardware assembly to the existing
[SquareRootDomains](SquareRootDomains.lean) partial relation, retaining the same
parameter, witness and incoming relation. Negative inputs have no root in this
relation, despite mathlib's total `Real.sqrt (-1) = 0`.
`nonnegative_defined_iff` preserves incoming definedness on nonnegative bounds;
`negative_absent` excludes roots when a certified upper bound is negative.
For mixed ranges, the existing `sqrt_values_defined_iff` still requires an admitted
nonnegative input. Numeric clipping cannot fill external holes or certify that all
inputs are defined. No continuity or existence follows just from returned bounds.

The native result is `Option (Bounds Float)`, not a domain-decorated value.
It returns unknown for entirely negative, reversed or nonfinite bounds and for
primitive failure. `none` alone is not an absence certificate. The negative-domain
proof requires decoded upper-bound evidence separately. There is no new Expr
constructor or automatic executable domain-tracking layer in this milestone.

## Native adapter and trusted boundary

The [x86_64 C adapter](hardware/adapter.c) rejects negative/nonfinite primitive
inputs and FTZ/DAZ, saves and holds the floating-point environment, sets FE_DOWNWARD
and FE_UPWARD for separate square-root evaluations, checks finite results and
restores the caller environment. Restoration failure aborts. The build uses
`-frounding-math -fno-fast-math -ffp-contract=off -fno-math-errno`; the final flag
permits native square-root code without C errno handling (errno is not this API's
error channel). The check requires `sqrtsd` in the object and rejects an unresolved
library sqrt call. The client rejects nonfinite original endpoints before clipping.

Signed zeros represent the same real zero; bit-level zero-sign equivalence is not
proved. Smallest-subnormal input is supported with gradual underflow enabled.
Square root does not need a new transcendental approximation/error budget.

The mathematical decoder, finite selection, primitive IEEE behavior, FFI, compiler,
physical processor and fenv implementation remain trusted, not verified. No theorem
identifies the logical throwing extern fallback with the C body. Native tests are
qualification evidence for that boundary, not its formal discharge. No new global
axiom, FP format, toolchain or application-build dependency is introduced.

## Source and C correspondence

Tupper's [thesis PDF](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=61),
§3.1, printed p.45 / PDF p.61, explicitly includes square root among correctly
rounded IEEE operations and requires correct rounding toward either infinity.
Section 3.1.1 supplies exact min/max. This source page was visually checked.

The precise three-branch partial-domain algorithm is in the
[SIGGRAPH 2001 paper](https://www.dgp.toronto.edu/papers/jtupper_SIGGRAPH2001.pdf#page=4),
§8, PDF p.4, also visually checked. Its negative branch marks absence; nonnegative
inputs retain incoming domain information; mixed inputs clear definite membership
and retain possible membership. The prior exact-real proof and source caveats are
in [generalized intervals](GENERALIZED_INTERVALS.md#square-root-with-domain-tracking).
The hardware theorem supplies conditional outward bounds for defined values; it
does not claim to implement all the paper's decorated-domain algorithm.

The current C [`gi_interval_sqrt`](https://github.com/funge/relgraph/blob/7fd4b39dc127dec3be1b96a46cf392d4bcd73d2b/src/interval.c#L509)
returns empty for empty or entirely negative input, clips the lower bound to zero,
and rounds the upper root upward. The Lean demo is inspired by this endpoint
construction but returns unknown for negative intervals and calls the primitive at
clipped zero too. The C routine's [`gi_raw_sqrt`](https://github.com/funge/relgraph/blob/7fd4b39dc127dec3be1b96a46cf392d4bcd73d2b/src/interval.c#L176)
and rounding helpers remain unverified, including other architectures and unbounded
values. Algorithm correspondence is not bitwise or C implementation equivalence.

## Checks and next integration

Run `./check.sh`, then `./hardware/check.sh` with the pinned Lean on PATH.
[Independent proof fixtures](tests/HardwareSquareRoot.lean) apply the actual theorem
to nonnegative and mixed intervals, preserve an external hole, reject negative
partial roots and a wrong primitive contract, and exercise domain conclusions.
[Independent expected-bit checks](tests/test_hardware_sqrt_vectors.py) square exact
binary64 values to establish enclosure and adjacent bounds without using sqrt.
This rational arithmetic is only a test oracle, never the interval runtime.

Native checks include `[1,4]`, sqrt(2), `[-1,4]`, `[-1,0]`, wholly negative input,
signed zero, smallest subnormal, largest finite value, NaNs, infinities, reversed
bounds and primitive negative-input rejection. A control verifies that sqrt(2)
raises INEXACT in each ambient rounding mode before the wrapper is required to
restore the caller's flags and mode. [Validation](VALIDATION.md) records results.
The next useful integration is a compositional hardware evaluator that preserves
these partial-domain conditions rather than treating every finite range as total.

This gia review carries the original relgraph PR #74 proof/runtime sources from
`f7cfea863529e48dffddc393cb9fb25d41ea9b03`, unchanged by relocation. The published
MIT baseline and broad GIA scope are preserved; relgraph remains an initial
application target. The original PR is not merged or closed by this transfer.
