# Retaining ordinary and affine bounds at the same input

[AffineConjunction.lean](AffineConjunction.lean) adds a portable proof/reference
layer alongside the existing [affine unary model](AFFINE_UNARY.md). It does not
change `AffineUnary.select`, its evaluator clients, the hardware backend or the
renderer. The goal is to retain a useful pointwise constraint even when its whole
range hull is too wide for the old selector.

## Representation and guarantees

`retain` returns a nonempty list of available affine bounds. Ordinary bounds are
embedded with the existing `LinearInterval.constant`. `Contains C t z` requires
**every bound in C to contain the same z at the same t**. No fit into a single
affine form and no hull approximation of the conjunction is performed.

- Both channels available: keep both, regardless of whole-hull inclusion.
- One unavailable: keep the surviving bound.
- Both unavailable: return `none`, meaning no bound is supplied.
- Available bounds that disagree are not dropped as a fallback. Their pointwise
  conjunction can be empty. This is a logical contradiction of the constraints,
  not an assertion that a backend failure proves an empty mathematical domain.
  Actual-value exclusion requires soundness of all supplied bounds.

`retain_sound` proves conjunction soundness from both certificates. `selected_mem`
shows that whatever the old selector chooses is one of the retained bounds;
`contained_in_selected` proves pointwise containment in that old result. This
inclusion requires successful old/new results, but holds even without a parameter
range assumption. Numerical soundness of square still requires `t ∈ [0,1]` and
an enclosed input witness. `ordinary_preserved` retains the existing ordinary
interval guarantee under those applicability hypotheses.

`add` maps the existing `LinearInterval.add` over every constraint. `add_sound`
proves sound composition, and `add_contained_in_selected` preserves containment
in the correspondingly extended old selected result. The `square` builder reuses
exactly the old ordinary multiplication and `squareCandidate`; only retention
changes. No new tangent is chosen or computed.

`square_add_image_sound` uses one actual input x for both x² and m*x+c.
`SquareAffineValues` and `relation_sound` keep that shared witness explicit.
They do not combine independently projected input sets. `domain_iff` preserves
external holes because square plus an affine function is total on each actual
real input; it does not declare the input relation total. Enclosure membership
alone never proves that the value occurs. For interval-valued uncertain inputs,
the bounds remain conservative and may lose correlations; no exact-image claim
is made. Mapping interval addition is enclosure propagation, not the exact
relational image of an intersection or a complete contradiction solver.

## Strict end-to-end control

The [fixture](tests/AffineConjunction.lean) reuses the normalized exact seed
`LinearInterval.exact ⟨-1,1⟩`, so `x=2*t-1` with `t ∈ [0,1]`.
The following are checked through the existing definitions, not assumed formulas:

| Existing computation | Result |
| --- | --- |
| Ordinary hull multiplication for square | `[-1,1]` |
| `squareCandidate` | lower `-2*x-1`, upper `1`; hull `[-3,1]` |
| Old `square` selection | constant `[-1,1]` |
| `image seed 2 0` | exact `2*x` |

Mapping existing affine addition over both retained bounds gives a constraint
with constant lower bound -1 for `x²+2*x`. Hence it excludes the entire closed
target `[-3/2,-5/4]` for all valid parameters. The old selected bound after the
same addition contains -3/2 at `t=1/4`, `x=-1/2`; disjointness of that old bound
therefore cannot certify the same exclusion. The actual value there is -3/4,
proved separately: the spurious bound member is not an actual image witness.

The ordinary bound also remains necessary: at `t=3/4`, the affine candidate
alone admits -1/2, while the old bound and retained conjunction exclude it.
This guards against simply replacing the ordinary result with the candidate.
Uncertain-input, negative-slope, missing-channel, contradiction and external-hole
controls are included.

A small exact reproducible comparison uses parameter values
`[0,1/4,1/2,3/4,1]` and the same target window. A sufficient disjointness query
certifies **3 of 5** with the old bound and **5 of 5** with the conjunction.
The count and query soundness are kernel-checked in the fixture. The conjunction
query succeeds when any retained constraint excludes the target; it is not a
complete general intersection solver. These are proof-side counts, not timings,
hardware results or renderer measurements.

"Old" here means the existing Lean `AffineUnary.square` followed by its affine
addition rule. Its ordinary baseline is intentionally conservative multiplication,
not sign-specialized squaring. No advantage over every ordinary interval method,
application prover, or production C implementation is claimed.

## Positive-domain control and a single-line obstruction

A supplemental fixture uses the exact normalized seed `x=1/2+t/2` on `[1/2,1]`.
Ordinary multiplication computes `[1/4,1]`, excluding `1/5`. The existing
`AffineUnary.propagate` constructs a midpoint tangent lower bound
`3*x/2-9/16` and an endpoint chord upper bound `3*x/2-1/2`. Retaining both
channels preserves the ordinary exclusion. Adding the same-witness affine term
`-3*x/2+5/8` gives `[1/16,1/8]` from the tangent/chord constraint. These are actual
portable representations and composition rules, with numerical soundness proved
for every input witness, not just isolated scalar inequalities. This fixture
supplies midpoint coefficients explicitly; it does not change the existing
left-endpoint `squareCandidate` algorithm.

The stronger obstruction applies to **any real affine lower bound** `L(x)=m*x+c`
sound for square on the whole interval. If it preserves the ordinary lower bound
at the left endpoint, `L(1/2)≥1/4`, soundness at `5/8` gives `L(5/8)≤25/64`.
Affineness then gives

`L(1) = 4*L(5/8)-3*L(1/2) ≤ 13/16`.

Consequently its shifted lower bound at `x=1` is at most `-1/16`, so that single
line cannot certify strict positivity. The retained conjunction can preserve
both deductions because it does not insist on a single affine lower bound.
Actual input witnesses attain `1/16` at `x=3/4` and `1/8` at `x=1`,
so the shifted range checks are not vacuous.
This is a representation-level obstruction under the stated endpoint-preservation
requirement, not a claim that an independent polynomial proof cannot show positivity.

## Tupper foundations and limits

The unchanged [chord](ENDPOINT_CHORDS.md) and [tangent](TANGENT_BOUNDS.md) modules
remain the mathematical foundation: thesis §2.9.3 gives the one-parameter affine
representation; §§3.3.10–3.3.12 provide the chord/tangent results used by the
existing unary model. Their source checks and remaining gaps stay visible in
[the concordance](THESIS_CONCORDANCE.md). In this example the existing candidate
uses the tangent at the left hull endpoint (-1), not a midpoint tangent.

Retaining the pointwise conjunction is a derived integration result, not a claim
to transcribe a new Tupper theorem or implement all generalized arithmetic. This
patch does not extend to reciprocal or square root, optimize line selection,
add a general expression interpreter, normalize arbitrary constraint lists, or
certify native execution. It adds no floating-point assumptions. The existing
adapter/compiler/hardware trust boundary is unchanged. Tupper foundational work
remains a separate research track; no unrelated source proof is mixed here.

Run `lake build AffineConjunction`,
`lake env lean tests/AffineConjunction.lean`, then `./check.sh` with the pinned
toolchain. See [validation receipts](VALIDATION.md). This milestone is local for
review; no push, PR or merge is part of this preparation.
