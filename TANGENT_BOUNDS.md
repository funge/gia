# Finite-domain tangent bounds

[TangentBounds.lean](TangentBounds.lean) formalizes the differentiable tangent
case discussed in Tupper §3.3.11 and the lower-bound dual of §3.3.12. It builds on
the merged [endpoint chord foundation](ENDPOINT_CHORDS.md). This is a real
mathematical result, not a new native floating-point operation or renderer feature.

For a contact p in [a,b] and a certified derivative d, define

    tangent(f,p,d,x) = f(p) + d(x-p).

`concave_upper` proves f(x) ≤ tangent(f,p,d,x) throughout [a,b] when f is concave
there. `convex_lower` proves the dual lower bound for convex f. The derivative
premise is `HasDerivWithinAt f d (Set.Icc a b) p`: only differentiability within
the interval at the contact is required. No derivative at other points, global
smoothness or interior-contact restriction is imposed. Mathlib's convex secant
slope inequalities justify the two sides of p; equality at p is immediate.

For singleton domains, `singleton` proves exact equality without curvature or
derivative premises and for any supplied slope. No division is performed by the
tangent definition. The proof at a general contact divides only by strictly
positive distances in the separate left/right secant cases.

## Composition and certified endpoints

`tangent_blend` identifies the tangent with interpolation of its endpoint
values. `outward_upper` and `outward_lower` therefore let callers enclose those
endpoint values outward and interpolate the certified results. These are explicit
real inequalities, not assumptions that a particular derivative oracle or FP
implementation computes them. In particular, rounding the slope in one fixed
direction is **not** enough: the multiplier x-p changes sign across p. Fixtures
show the resulting failures for the linear function f(x)=x.

`convex_sandwich` combines a lower tangent with the exact upper chord;
`concave_sandwich` combines a lower chord with an upper tangent. Both use the same
normalized parameter and interval and reuse the existing chord theorem. The
square fixture yields t-1/4 ≤ t² ≤ t on [0,1]; a negative-square fixture checks the
upper-tangent dual. Endpoint contacts, singleton behavior and a genuinely
outward lower endpoint pair are also checked.

## Source and limits

The [original thesis](https://www.dgp.toronto.edu/~mooncake/thesis.pdf), printed
p.79 / PDF page 95, was rechecked visually from the existing graphing repository
copy. In §3.3.11 Tupper first gives a secant upper bound outside its two sample
points for a concave function, then describes the differentiable limiting case
as matching both value and derivative at the contact. This module formalizes
that tangent case directly via ordinary real calculus. §3.3.12 on printed p.80 /
PDF page 96 supplies the lower-bound duality context.

This is a restricted finite closed-domain counterpart, not a formalization of
infinitesimals, all relational curvature charts, the finite-secants/discrete-neighbor
case, missing domain endpoints or extended-real models. Tupper also discusses
choosing the midpoint for constant-weight optimality and refers to §3.4.3.
That weighted criterion has **not** been formalized here. In particular, the
pointwise least/greatest claim from the chord milestone cannot be transferred
to tangents: the negative-square tangents at 0 and 1 cross. A fixture proves this
counterexample explicitly. No optimal contact-selection algorithm is claimed.

There are no new FP assumptions, axioms, native changes, hardware derivative
contracts or C verification claims. A later hardware implementation would need
to certify value/derivative information and the entire tangent arithmetic under
the approved contract; this proof alone does not supply such an implementation.
The [concordance](THESIS_CONCORDANCE.md) records this partial source coverage.

Run `./check.sh` with the pinned Lean toolchain. The
[semantic fixtures](tests/TangentBounds.lean) are freshly compiled and audited by
the complete gate; [validation receipts](VALIDATION.md) state exact results.
