# Guarded hardware quotient composition

This layer composes the [dual-track polynomial evaluator](HARDWARE_EVALUATOR.md)
with the existing [finite hardware division](HARDWARE_DIVISION.md). It evaluates
native directed binary64 arithmetic. Rational arithmetic is used only in the
independent test oracle and mathematical fixtures, not as the executable backend.

## Representation and result policy

[HardwareQuotientProgram.lean](HardwareQuotientProgram.lean) reuses polynomial
leaves (constants, one shared variable, addition, subtraction and multiplication).
A small outer grammar composes these blocks with addition, subtraction,
multiplication and division. Each leaf runs the existing ordinary and affine
tracks and intersects their successful bounds. At every outer node:

- the ordinary baseline uses the children's ordinary bounds;
- the refined calculation uses the children's combined bounds;
- two successes are intersected; one success survives; two failures are unknown;
- a child conflict propagates, and disjoint successful outputs remain a conflict.

Division requires a denominator hull strictly below or strictly above zero.
Touching zero, crossing zero, nonfinite values, overflow or unsupported native
conditions return unknown. Unknown is never a claim of nowhere-definedness.
The code retains a separate ordinary result for diagnostics even when a conflict
is reported; callers must inspect the refined result and must not treat that
ordinary field as recovery from a contradiction.

Quotient outputs carry only interval bounds. No affine quotient form or quotient
correlation is fabricated. Polynomial block boundaries are explicit; arithmetic
outside them uses ordinary interval operations even when no division occurs.
This avoids modifying or duplicating the existing polynomial traversal. A future
automatic partitioning pass would need its own specification.

## What Lean proves

[HardwareQuotient.lean](HardwareQuotient.lean) uses a relational `Value` semantics.
A division constructor requires the actual real denominator to be nonzero, so
Lean's totalized real division does not silently supply values at poles.
`value_unique` supplies the common semantic witness needed for intersection.

`eval_cert` proves compositional certification: every successful ordinary or
refined bound contains a defined value, and sound tracks cannot conflict.
Its premises are the existing comparison/min/max contracts, sound operations,
and certificates for polynomial leaves actually present in the expression, at
the real point being considered. `polynomial_leaf_cert` derives those leaf
certificates from an interpreted polynomial value and the prior ordinary/affine
enclosure results at a common parameter in [0,1]. Applying these premises at
each represented input point gives enclosure throughout the input interval.
This is conditional on literal interpretation and leaf enclosure; it is not a
new proof of native Float decoding or an unconditional native definedness claim.

`guarded_division_sound` derives the division operation certificate directly from
`HardwareDivision.assembleGuarded_encloses`, including nonzero definedness. The
other operation certificates lift the existing interval operation results.
`eval_preserves` proves that a successful ordinary result is retained and its
combined bound is a subset of that result. This preservation theorem assumes
sound consistent contracts: a deliberately contradictory backend is exposed as
conflict, not concealed to preserve an ordinary output.

No new floating-point assumption, axiom, decoder, adapter operation or compiler
flag is introduced. The existing directed rounding, finite comparison/min/max,
zero interpretation and native adapter/compiler/IO/hardware boundary remains
explicit. Kernel proofs concern the pure traversal and conditional operation
contracts; native tests qualify, but do not verify, their implementation.

## Examples and independent controls

On t in [0,1], let d(t) = 1/2 - t(1-t). The ordinary denominator is [-1/2,1/2],
so ordinary division is unknown. The shared-parameter bound is [1/4,1/2], and
`1/d(t)` returns **[2,4]**, width 2. Its negative-denominator counterpart returns
[-4,-2]. Addition, multiplication and a nested quotient compose these bounds.

For `1/(1/2-t)`, both paths remain unknown. The [Lean fixture](tests/HardwareQuotient.lean)
proves it undefined at t=1/2 but defined at t=0. It also proves that a certified
evaluation at the midpoint must return unknown. In contrast, subtracting two
copies of the safe quotient returns [-2,2], not [0,0]: that is an explicit control
for loss of quotient correlation, not a cancellation claim.

The [native client](hardware/Main.lean) tests 12 expressions on seven intervals,
including zero endpoints/singletons, negative inputs, extreme finite values,
overflow, both fallback directions and nested operations. The independent
[exact-rational oracle](hardware/check_quotient.py) reproduces directed endpoint
rounding and checks real partial semantics at 17 rational sample points per
successful output. Synthetic native controls inject both child conflicts and
disjoint operation outputs. Sampling supplements the universally quantified Lean
proof and is not a replacement for it. No runtime optimization or speed claim is
part of this milestone.

## Tupper and implementation correspondence

The [thesis](https://www.dgp.toronto.edu/~mooncake/thesis.pdf) §§2.9.3–2.9.5 motivate
shared-parameter linear inclusion; §3.2.22 (printed p.64 / PDF p.80) treats division
via reciprocal and multiplication, and §3.2.26 (printed p.68 / PDF p.84) treats
partial binary functions. This wrapper and its two-track policy are derived
project integration, not a transcription of a generalized model-construction
chart. It handles only finite zero-excluding quotient hulls, not poles with
unbounded outputs, disjoint ranges or automatic external-domain inference.

The initial C target is
[`gi_interval_div`](https://github.com/funge/relgraph/blob/3975a5e1696e59c337093435ffce0748f074a057/src/interval.c#L461)
(the pinned implementation reference may require repository access). That code
uses a rounded reciprocal followed by multiplication; this native client uses
four directed quotients. Neither equal bits/tightness nor C implementation
correctness follows from the Lean proof. GIA builds without that checkout;
[coverage records](OPERATION_COVERAGE.md) describe the optional API comparison.

Run `./check.sh` and `./hardware/check.sh` with the pinned Lean toolchain on PATH.
See [validation receipts](VALIDATION.md) for exact results. This milestone
is based on merged evaluator PR #12, main commit
`de4e1a2fe5d3a586c82d173f0aa4b5acf7239313`. Its review diff contains only guarded
quotient composition and its checks/documentation.
