# Unary affine propagation from certified lines

[AffineUnary.lean](AffineUnary.lean) connects the finite-domain chord and tangent
proofs to the existing uncertain one-parameter `LinearInterval` representation.
This is a portable mathematical composition layer and exact reference fixture.
It does **not** add a rational replacement for the hardware runtime, an AST
constructor, a native adapter, or a floating-point assumption.

## Contract and composition

`propagate_sound` accepts a possibly partial relation `F x z` and certified affine
lower/upper lines valid for every related value whose input lies in the input
hull. Existing affine multiplication and addition propagate those lines, including
negative slopes and uncertain endpoints, at the **same** parameter in [0,1].
Endpoint ordering is checked when assembling the result. Success of this check
alone does not certify the supplied lines; the theorem requires their enclosure
proof. Failure means unknown, not nowhere-defined.

`select` retains an affine candidate only when its whole hull fits inside a
successful ordinary result. Otherwise it embeds the ordinary interval as a
constant form. With only one successful track it uses that track; two failures
produce unknown. `select_sound` requires sound candidates, and
`ordinary_preserved` proves ordinary success is never lost or widened. This is
not intersection: intersecting two affine bounds generally gives piecewise
bounds. The conservative policy may discard useful local refinements. It is not
a runtime checker for contradictory uncertified models; the existing hardware
evaluator and its contradiction handling are unchanged.

`UnaryValues` carries the actual common input witness. `domain_sound` preserves
an existing `DomainBounds` only with an explicit totality certificate for `F` on
the input hull. Its upper-domain and range claims use only actual related values;
its lower-domain claim needs this totality certificate. Thus external holes stay
holes, while a partial operation cannot inherit definite definedness without
proof. No automatic domain or continuity inference is added.

## End-to-end square

For a finite hull [a,b], `square_support` proves

    2*a*x - a^2 ≤ x^2 ≤ (a+b)*x - a*b.

The lower bound invokes `TangentBounds.convex_lower` with the proved derivative
of square at a; the upper invokes `EndpointChords.convex_upper`. Singleton and
mixed-sign domains are included. `square` propagates these lines and uses ordinary
hull multiplication as fallback. That baseline is deliberately conservative for
square and can include negative numbers on a zero-crossing domain. No optimal
tangent selection or universal precision advantage is claimed.

[Semantic fixtures](tests/AffineUnary.lean) prove universal enclosure for uncertain
coefficients, nested square with the same parameter, negative-slope propagation,
singletons, mixed-sign fallback, one-track failure and two-track failure. For
x=1/2+t/2, the result has lower endpoints (1/4,3/4) and upper endpoints (1/4,1).
At t=1/2 its width is **1/8**, versus **3/4** for ordinary hull multiplication.
This exact comparison is not a runtime benchmark or a hardware measurement.
Nested squaring retains an external hole at t=1/2. A reciprocal-at-zero control
shows why whole-hull totality cannot be omitted.

## Source and implementation correspondence

Tupper's [1996 thesis](https://www.dgp.toronto.edu/~mooncake/thesis.pdf), §2.9.3,
provides the endpoint affine representation; §§3.3.10–3.3.12, printed pp.78–80
(PDF pages 94–96), provide chord and tangent bounds and their duals. The repository
PDF was checked for those source results in the preceding milestones. This new
composition is a **derived restricted integration**, not a claim to formalize the
complete generalized unary chart algorithm or its weighted approximation rule.
See [chords](ENDPOINT_CHORDS.md), [tangents](TANGENT_BOUNDS.md) and the
[concordance](THESIS_CONCORDANCE.md).

The initial C comparison is exponent two of
[`gi_interval_pow_nonnegative_integer_exponent`](https://github.com/funge/relgraph/blob/3975a5e1696e59c337093435ffce0748f074a057/src/interval.c#L628).
That implementation has sign-specialized ordinary power bounds; our fallback is
plain multiplication, so neither algorithm identity nor C correctness is claimed.
The pinned implementation link may require access; building gia does not.
Other powers, hardware unary propagation, derivative computation and rounding of
model coefficients remain outside this milestone. Hardware integration must
certify rounded line bounds, including displacement signs; naively rounding a
derivative in one direction is insufficient. The existing adapter/compiler/
hardware trust boundary remains unchanged.

## Verification

Run `lake build AffineUnary`, `lake env lean tests/AffineUnary.lean`, then
`./check.sh` with the pinned toolchain on PATH. The module participates in named
and namespace-wide axiom allowlisting; the fixture is registered in the full
semantic gate. See [validation receipts](VALIDATION.md). Native backend files
are unchanged and no hosted CI is added.
