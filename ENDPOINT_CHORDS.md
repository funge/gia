# Convex and concave endpoint chords

[EndpointChords.lean](EndpointChords.lean) formalizes the finite closed-domain
endpoint construction from Tupper §3.3.10, its lower-bound dual (§3.3.12), and the
cubing example in §3.3.14. This is a general real-arithmetic foundation, independent
of graphing, rendering, the hardware evaluator and the guarded-division PR.

## Statements and hypotheses

For real a ≤ b and parameter t in [0,1], write

    blend(a,b,t) = (1-t)a + tb.

For a real-valued function f convex on [a,b], the exact endpoint chord
`blend(f(a),f(b),t)` bounds `f(blend(a,b,t))` above. If f is concave, it bounds
that value below. No differentiability or additional continuity premise is needed:
mathlib's `ConvexOn` / `ConcaveOn` supplies the appropriate weighted inequality.
`parameter_exists` proves that every point of the closed interval has this
normalized representation, including the singleton case.

`least_affine_upper` compares the exact chord with **every** affine majorant
x ↦ mx+c on the interval. The comparison follows from the two endpoint constraints
and nonnegative interpolation weights. `convex_optimal` additionally constructs
an affine majorant realizing the chord, and proves it pointwise least among all
such majorants. The concave dual `concave_optimal` constructs a pointwise greatest
affine minorant. These statements concern this entire finite closed interval;
they are not extrapolation or global approximation claims.

The interpolation definition never divides. When a=b, `blend(a,a,t)=a` and the
exact chord is f(a) for every t, without any curvature premise. The affine
existence proof chooses slope zero in this case. Only the nondegenerate branch
uses the ordinary secant slope (f(b)-f(a))/(b-a). Coefficients are not asserted
unique on a singleton, even though the represented value is exact.

## Certified endpoints versus exact optimality

`outward_upper` accepts arbitrary real u≥f(a), v≥f(b) and proves that their chord
is a sound convex upper bound. `outward_lower` accepts l≤f(a), k≤f(b) for the
concave lower bound. The endpoint inequalities are explicit certificates supplied
by the caller; this module does not assume or implement an endpoint oracle.
`qaffine_upper` / `qaffine_lower` connect these real results directly to the
existing [QAffine endpoint representation](LinearIntervals.lean).

Outward certification does **not** preserve the exact-endpoint optimality claim.
A fixture for f(x)=x² on [0,1] shows that endpoint bounds 1/10 and 11/10 remain
sound but their chord lies strictly above the exact chord. The module introduces
no new floating-point assumptions and does not execute a hardware endpoint or
chord algorithm. Existing directed-rounding contracts may later supply endpoint
certificates and an enclosure of interpolation arithmetic; that integration is
not claimed here.

## Source correspondence and transcription control

The original [thesis PDF](https://www.dgp.toronto.edu/~mooncake/thesis.pdf) was
inspected using the existing copy in the graphing repository, not re-downloaded:

- §3.3.10, printed pp.78–79 (PDF pages 94–95), chooses the two domain-endpoint
  values, proves the chord an upper bound for a concave-up function, and argues
  optimality from the endpoint constraints.
- §3.3.12, printed p.80 (PDF page 96), refers lower bounds to the upper-bound
  rules. This module states and proves the concave dual explicitly.
- §3.3.14, printed p.80 (PDF page 96), gives the cubing example. Its lower
  parameter branch (-2+t)³ is concave; its upper branch (4-t)³ is convex.
  These annotations are checked against the PDF because the Markdown
  transcription can damage the curvature symbols.

The formal hypotheses are **narrower and differently expressed** than Tupper's
relational property-chart presentation: f is real-valued and convex/concave on a
finite closed interval, including both endpoints. The general affine domain is
reparameterized to [0,1]. There is no proved equivalence here between mathlib
convexity and Tupper's full ψ₂ charts, no open/missing-endpoint completion, no
extended-real/infinite endpoint model, and no §3.3.11 tangent or discrete-neighbor
construction. The pointwise least/greatest theorem makes the finite continuous
interval meaning of the source's optimality argument precise; it is not a claim
to formalize every source notion of weighted optimality.

## Cubic regression and validation

`cubic_lower_concave` and `cubic_upper_convex` prove the source curvature facts
using mathlib convexity of the cube on nonnegative reals and affine changes of
variable (plus sign reversal for the lower branch). Applying the general chord
theorems gives the endpoint lines; monotonicity of the real cube then proves

    0 ≤ α ≤ 1,  -2+α ≤ x ≤ 4-α
      ⇒ -8+7α ≤ x³ ≤ 64-37α.

Thus `cubic_source_enclosure` is an integrated application of the new foundations,
not only an isolated polynomial identity. The [semantic fixture](tests/EndpointChords.lean)
checks sharp endpoint values, strict interior slack, the square's exact/outward
chords, singleton behavior, wrong-side rejection and failure of extrapolation.
The tests and source module are registered in the existing enforced axiom audits.
Run `./check.sh` with the pinned Lean toolchain on PATH; see
[validation receipts](VALIDATION.md). No renderer integration, native path change,
new package pin or axiom policy change is included.
