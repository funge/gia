# Domain-compatible descriptor conversion

Source: Tupper §§2.11.2–2.11.3, printed p.35 /
[PDF p.51](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=51), visually
rechecked. The source requires downward/upward numeric descriptor demotions to
preserve classifications, and permits different domain-description functions.
This package proves an actual mathematical conversion instance beyond finite
affine coefficients; it does not assume that every numerical conversion preserves
every classifier or infer an unspecified exceptional operation.

## General criterion and a discharged conversion

[DescriptorDemotion.lean](DescriptorDemotion.lean) reuses `exactInputDomain` to
interpret descriptor set S and predicate P. Its definite condition is
`S.Nonempty ∧ ∀x∈S, P x`; possible is `∃x∈S, P x`. The existing nonempty guard
prevents vacuous definite truth. This is conservative domain information at each
parameter, not a claim that both Boolean outcomes occur in the caller's narrower
actual domain.

For S⊆T at each parameter, `widen_refines_iff` proves the EXACT remaining condition
for classification refinement in this model:

```
T.Nonempty → (∀x∈T, P x) → S.Nonempty.
```

Possible outcomes already widen by inclusion. The condition is needed only when
the target would assert definite truth. Nonempty source fibers suffice; globally
preserving emptiness also suffices. No continuity or monotonicity of P is needed,
because the interpretation quantifies over the whole admitted set.

`integer_hull_refines` instantiates this with `NumberPromotion.hull`, the existing
least outward interval with extended integer endpoints. Its existing soundness
supplies inclusion, and `integer_hull_nonempty` proves nonemptiness equivalence
using soundness and the existing empty-hull theorem. Thus the conversion is
proved for arbitrary real sets, including disconnected, open, empty and unbounded
ones, and arbitrary real predicates. This is a semantic construction, not an
automatic executable predicate classifier. Infinite endpoints are bounds on real
descriptors, not literal infinite values or new IEEE results.

`guarded_integer_compatible` keeps the same actual descriptor x and external
predicate A while intersecting the converted description with the original G.
It proves compatibility with `A ∧ P x`; x is not replaced by a rounded endpoint.
An external hole remains a hole. This is conversion of domain information, not
creation of expression values or loss of partial-operation obligations.

## Checked failure cases and repairs

- Inclusion alone fails under the explicit empty-fiber convention: empty S
  widened to {0}, with P=True, would replace false-only information by definite
  truth. This is a counterexample to an UNGUARDED generalization, not a claim
  that Tupper's well-formed nonempty intervals violate his rule. The iff above
  is the weakest additional condition under the stated subset premise.
- Rounding a descriptor point 1/2 downward to zero changes the nonzero predicate.
  Whole-set outward conversion instead gives [0,1], changing definite nonzero
  to mixed information while retaining compatibility with the actual 1/2.
- `boundImage` uses the existing tagged `ExceptionalComparisons.bound` map and
  keeps successful bound outputs. For the source family {lambda, finite 0},
  dropping lambda and classifying remaining bounds as defined changes mixed
  definedness to definite truth. `dropping_lambda_counterexample` rejects this
  refinement. This is not a source-prescribed promotion we claim to refute.
- `bound_defined_iff` proves that this existing map succeeds iff the tag is not
  lambda. `retained_tag_domain` proves the sound repair: keep the original
  tag-domain description beside the numeric projection and check compatibility
  against the SAME tag. Infinities map to bound endpoints; lambda maps to none.
  No numerical comparison, arithmetic, or IEEE table is used to infer this.

[Fixtures](tests/DescriptorDemotion.lean) check the exact hull of {1/2}, strict
loss of definite nonzero information, an unbounded mixed descriptor, empty
conversion, external holes, a retained nonzero witness, retained lambda
compatibility and the distinction between infinite tags and lambda.

This closes a concrete general domain-description demotion obligation and the
specified projection boundary. It does not formalize all exceptional carriers,
all source rounding formats, arbitrary classification algorithms, or the full
Chapter 2. It adds no FP assumption or production/native/default change. Review
with family conversion unit 3 after domain and extended-bound foundations.
