# Exact closed hulls of attainable real outputs

[ExactImageHull.lean](ExactImageHull.lean) develops the finite, nonempty, bounded
part of Tupper §§2.7.3–2.7.4 and §2.8, printed pp. 24–26 /
[PDF pp. 40–42](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=40).
Those pages were visually checked in the existing source copy for this milestone.
No PDF or transcription is added or required by the build.

The source distinguishes the inclusion property (containing every real output)
from the interval extension obtained by infimum and supremum, and then from
outward demotion to floating-point endpoints. This module preserves those three
layers. It is a restricted finite real counterpart, not the full source's
extended-real system. See the [Chapter 2 checklist](CHAPTER2_CHECKLIST.md).

## Generic hull and actual image

For a real output set `S`, `hull S = Set.Icc (sInf S) (sSup S)`.
Mathlib's conditionally complete order facts supply the infimum/supremum laws;
we do not reconstruct real completeness.

- `sound`: bounded-above and bounded-below `S` is contained in its hull.
- `ordered`: nonempty bounded `S` has `sInf S ≤ sSup S`.
- `least`: if nonempty `S` is contained in any closed real interval `[l,u]`, its
  hull is contained in that interval. The proposed enclosure itself supplies
  finite bounds. `enclosure_iff` combines leastness and inclusion.
- `mono`: if nonempty `S ⊆ T` and `T` is bounded on both sides, then
  `hull S ⊆ hull T`. The subset also inherits boundedness; no assumption that
  the two sets share independently chosen input coordinates is made.
- `eq_of_attained`: if an enclosing interval's two endpoints actually belong
  to `S`, that interval is the hull. This additional attainment premise is used
  for closed-interval addition, never asserted for arbitrary output sets.

`values D R = {z | ∃ a ∈ D, R a z}` retains an actual admissible input witness.
`R` may be partial or multivalued. No output is supplied when there is no such
witness. `values_total` identifies the total-function specialization with
mathlib's image `f '' D`; `values_refine` preserves the same input witness under
admissible-domain/relation refinement. In particular, nonempty **inputs** alone
do not imply nonempty **outputs** for partial relations.

These theorems concern the least **closed interval** enclosing the image, not
exact membership in the image. Hull membership must not be used as an existence
certificate. The definition is a mathematical, noncomputable specification,
not an algorithm for finding the extrema of an arbitrary function.

## Independent interval addition and outward results

`sums I J` explicitly takes admissible pairs `(x,y)` with `I.Contains x` and
`J.Contains y`, and returns `x+y`. This worked operator uses independent
operands deliberately. `sums_enclosed` reuses existing `add_encloses`.
`sums_endpoints` supplies the attained lower/lower and upper/upper sums.
`add_exact` then proves:

```text
hull (sums I J) = {z | (I.add J).Contains z}
```

Thus the cast of the existing rational `QInterval.add` is the exact closed real
hull for those independent interval operands. This does not claim the same
hull for dependent expressions bounded by those intervals.

`rounded_add_contains_hull` reuses `rounded_add_encloses` under its two local
outward inequalities. `decoded_contains_hull` proves a general bridge: one fixed
finite decoded interval enclosing every output of a nonempty set also encloses
its hull. Decoding uniqueness identifies the same endpoints for all witnesses.
`hardware_add_contains_hull` applies that bridge to the existing
`HardwareAddition.assemble_encloses` theorem, with the actual observed lower and
upper paired-call contracts, successful assembly, and four input endpoint-decoding
premises matching the rational intervals.

There is no new arithmetic soundness proof, no new FP assumption, and no claim
that success is automatic, that returned bounds are the tightest representable
ones, or that the result has a particular bit pattern. Native adapter, compiler,
rounding-mode and hardware trust remain unchanged. No C/FFI or hot-path code is
modified; no native executable or timing benchmark is part of this milestone.

## Semantic controls and limits

[The fixture](tests/ExactImageHull.lean) proves:

- `(0,1)` has hull `[0,1]`, but neither hull endpoint is attained;
- `{0,2}` has hull `[0,2]`, but the interior point `1` is unattainable;
- singleton and zero-interval behavior, and hull containment under refinement;
- independent `[0,1] + [-1,0]` has hull `[-1,1]`, while the actual shared-input
  image `t + (-t)`, `t ∈ [0,1]`, is `{0}` with hull `[0,0]`;
- the guarded reciprocal relation on inputs `{0,1}` has output set `{1}`:
  the zero input contributes no value, even though Lean's total division syntax
  can appear inside the guarded formula;
- a loose outward addition result may contain `-1` while the exact `[0,2]` hull
  does not; concrete real-valued observed pairs discharge the existing hardware
  contracts, and an unavailable observation does not assemble a bound.

Empty output sets are explicitly ineligible for the leastness/exactness workflow;
unbounded and exceptional values are deferred. Mathlib assigns infimum/supremum
terms even outside our hypotheses; this module gives them no interval semantics
there. General n-ary extension/demotion algorithms, §2.9.2 three-valued logic,
extended-real endpoints and native refinement remain open. This does not mark
§§2.7–2.8 or Chapter 2 complete, nor does it replace the existing two-interval
rational `BasicIntervalOps.hull_least` special case.

With the pinned toolchain, run `lake build ExactImageHull`,
`lake env lean tests/ExactImageHull.lean`, and `./check.sh`. Supply
`RELGRAPH_CHECKOUT` explicitly for the optional pinned API comparison, as in
[operation coverage](OPERATION_COVERAGE.md). Results are recorded in
[validation receipts](VALIDATION.md).
