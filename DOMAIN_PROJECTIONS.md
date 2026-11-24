# Finite projections and numeric domain descriptions

This slice links Tupper's §2.7.2 optimistic/pessimistic Boolean projections
(printed p.24 / [PDF p.40](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=40))
to finite numeric descriptions in §2.11 (printed pp.34–36 / PDF pp.50–52).
The transcription was read first; the original PDF projection table and the
printed p.34 domain-membership passage were visually checked. The existing
§2.11.4 source review is retained. Non-strict comparison and the threshold
clients below are derived finite counterparts, not additional equations
claimed to be printed in the source. Equality/inequality comparison is supplied by the
[finite package](FINITE_COMPARISONS.md); no exceptional interval comparison calculus is claimed.

## Exact claims

[DomainProjections.lean](DomainProjections.lean) reuses `StrictComparison.Truth`,
its `lower`/`upper`, `BooleanComposition.neg`, and `DomainConstraints`.

* `pessimistic_iff`: `v.lower = true` iff every Boolean admitted by `v` is true.
  `optimistic_iff`: `v.upper = true` iff true is admitted. These are precisely
  the source projection tables, without introducing a duplicate truth type.
* `domain` interprets these projections as existing definite/possible predicates.
  `description_domain` recovers the original description; `domain_compatible`
  equates the existing semantic compatibility contract with membership of the
  actual definedness Boolean. `domain_refines` transports information inclusion.
* `compareLE I J = neg (compare J I)` has exact image `leOutcomes I J` for
  **independent** real operands in finite ordered rational intervals. Its true-only
  guard is `I.hi ≤ J.lo`, false-only guard `J.hi < I.lo`. Reversal gives the
  greater-or-equal relation; existing reversed strict comparison already covers
  greater-than. This does not make marginal comparisons exact for correlated inputs.
* `numericImage f I` is the image of **all** real values contained in I.
  `numeric_projections` identifies optimistic projection with existence of a
  satisfying value and pessimistic projection with universal satisfaction,
  **only under exact image equality**. A conservative mixed result alone has no
  such attainment guarantee.
* `numeric_compatible` needs only sound classification and an actual contained
  same-input value. `guarded_numeric_compatible` keeps an external input predicate
  and requires numerical enclosure only where it holds. A representative value
  outside that domain cannot fill a hole.
* `numeric_refines` and `numeric_domain_refines` prove that enlarging an interval
  preserves description inclusion for an exact whole-image classifier, including
  a nonmonotone real predicate. They do not claim that every sound classifier is
  monotone, that the classification label is unchanged, or that evaluating the
  predicate at just the two numeric endpoints is adequate.
* `above q` and `atLeast q` are executable finite rational threshold classifiers,
  proved equal to the actual real predicate images. `threshold_compatible` connects
  both to existing DomainBounds. The real `gtPredicate`/`gePredicate` and general
  semantic description are proof-side classical functions, not hardware routines.
* `sqrt_constraint_compatible` composes a nonnegative numeric description and
  an external input guard with the existing **partial** `SqrtValues` relation.
  The numerical input is one shared witness, and compatibility with its external
  predicate is supplied explicitly. This is a domain result; existing square-root
  range proofs are reused rather than replaced. It asserts no automatic range
  evaluation, native execution or general operation-domain inference.

## Boundary and failure controls

[Fixtures](tests/DomainProjections.lean) check the six projection table entries,
strict/non-strict touching and singleton boundaries, negative separation, exact
comparison images, correlated `x ≤ x` versus independent mixed marginals,
strict versus closed threshold at zero, and widening from definite to mixed.
The exact numerical projection theorem is exercised on a crossing-zero interval.

For the nonmonotone predicate `x ≠ 0`, both endpoints of [-1,1] classify true,
but the admitted interior zero classifies false: an endpoint-only all-true result
would be unsound. Separately, an intentionally loose yet sound constant-true
classifier returns mixed on singleton inputs and true-only elsewhere; this
falsifies monotonicity inferred from soundness alone. The generic widening proof
uses its stronger exact-image premise explicitly.

The actual partial square-root controls include a defined zero, a negative input
with no value, and an externally excluded zero that remains undefined. No totalized
`Real.sqrt` behavior at negative inputs is used to claim definedness.

## Scope and ordering

Builds on the merged Boolean composition and shared-parameter domain-constraint
results (#32 and #33). No native, C/FFI, production defaults,
floating-point assumptions, timing or renderer changes. Finite ordered nonempty
QIntervals only: no missing/exceptional endpoints, lambda encoding, general
numeric descriptor generator or full §2.11 extension/demotion construction.
The source's exceptional-value membership conventions are not settled by these
real-valued compatibility theorems.

```sh
lake build DomainProjections
lake env lean tests/DomainProjections.lean
./check.sh
```

See [completion criteria](CHAPTER2_COMPLETION.md), [checklist](CHAPTER2_CHECKLIST.md),
[concordance](THESIS_CONCORDANCE.md) and [validation](VALIDATION.md).
