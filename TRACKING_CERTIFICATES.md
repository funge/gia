# Sufficient continuity tracking and exact strict-domain closure

Source: Tupper §2.12, printed pp.36–37 /
[PDF pp.52–53](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=52).
The local transcription was read and both original PDF pages visually checked.
The weak definition prints a composite-to-recursive implication; the strong
one prints an equivalence. The next page defines semantic continuity by a limit
and its checkable predicate by continuity conjoined with every child flag.
It then calls continuity weakly checkable and definedness strongly checkable.
The nearby square-root examples concern domain descriptions, not a proof of
this continuity implication. None of this establishes an intended correction.

## Two readings remain distinct

1. **Literal semantic reading.** Apply the printed arrow to the printed
   continuity predicate. This is refuted even for total unary real functions
   with true leaf flags. The existing [counterexample](tests/PropertyComposition.lean)
   is preserved: a constant outer function hides a discontinuous ±1 jump.
   The new control uses the nonconstant outer function `g(t)=t²`; the composite
   is identically 1, while the child is discontinuous somewhere on [0,1].
   Therefore composite continuity cannot force recursive continuity checks.
   A strong iff for that interpretation fails as well; the source does not
   claim strong continuity, but its weaker printed direction already fails.
2. **Conservative structural reading / corrected sufficient rule.** Successful
   recursive checks imply semantic continuity, with explicit definedness and
   domain-mapping premises. Failure is inconclusive. This is mathematically
   sound, but it changes the direction and meaning of the printed weak claim.
   The recursive construction prose is compatible with a conservative checker;
   it does not prove that this was the author's intent. We do not relabel this
   rule as a faithful proof of the printed weak definition or silently replace it.

The original unary pointwise `recursive_checks_suffice` remains in the fixture.
The production finite-arity rule reuses `FiniteProperties.continuous_composeN`:
all children have defined continuous real representatives on S; the outer
partial operation has a defined continuous representative on T; every actual
child tuple at a common x in S lies in T. Its conclusion is continuity with
definedness on S. This is sufficient, not necessary, as the masking examples
show. It is a relative/setwise rule, not an unrestricted equivalence with the
source pointwise predicate. Empty S supplies no value or property at an
arbitrary point outside S. The outer-domain and same-tuple obligations remain
explicit; no numerical enclosure alone supplies them.

## Sound property-description transport

[TrackingCertificates.lean](TrackingCertificates.lean) reuses DomainBounds and
PartialProperties.Tracks. If C is a sufficient certificate for a semantic
property P, a sound description of C cannot in general be copied as a description
of P: C may be false while P is true. `sufficient Q` therefore keeps
`Q.definite` and sets `possible` to True. This is a conservative construction,
not a claim of the most precise available description.

- `sufficient_compatible`: compatibility with C and C→P gives compatibility of
  `sufficient Q` with P.
- `sufficient_tracks`: the same rule under an admissibility relation A, preserving
  the same parameter and witness. A false certificate does not exclude P.
- `continuous_description`: instantiates that transport with the existing
  finite-arity continuity theorem and its outer-domain premises.

`masked_check_requires_unknown` uses the actual square/jump counterexample:
the exact false recursive-certificate description is **not** compatible with
the true semantic property, while the sufficient description is compatible.
Thus the implementation fixes a concrete property-description error, not just
the direction of an isolated logical implication. Domain definedness and
semantic continuity remain separate properties.

## Independent exact domain-description closure

Because authorial intent is unresolved, the same bounded milestone proves a
source-independent positive obligation supported by strict definedness in
§2.12.1 and the extra partial-operation guard of §2.11.4 (printed pp.35–36).
It reuses `composeN`, `composeN_defined`, and `partial_guard_compatible`; no
new evaluator or domain-description type is introduced.

`OuterDefined g f x` quantifies over the **actual** child tuple v at x:
if every `f i x = some (v i)`, then g v has a result. The exact theorem is

```
(∃ z, composeN g f x = some z) ↔
  (∀ i, ∃ y, f i x = some y) ∧ OuterDefined g f x
```

The outer guard alone can be vacuous when a child is missing, so its conjunction
with child definedness is essential. Both directions are proved, including
arity zero. `defined_description` combines existing compatible child and guard
descriptions into a compatible description of actual composite definedness at
the same parameter/input. The guard description is a supplied, proved premise,
not inferred by a new automatic checker. No independent tuple choices, external
hole filling, or totalized division is permitted. The strong conclusion applies
to this strict deterministic partial composition, not to lazy evaluation that
can discard a missing argument.

[Fixtures](tests/TrackingCertificates.lean) cover a guarded reciprocal, actual
nonzero results, zero exclusion, a missing argument to a constant outer function,
a nullary missing result, a positive continuity certificate, and failed checks
compatible with either property outcome. These supplement the preserved and
strengthened source-arrow counterexamples.

## Remaining scope and verification

No full recursive property AST, exact property-description generator, or
necessity of the continuity certificate is claimed. Existing finite-arity local constancy is a separate
sufficient theorem with explicit point definedness; it is not the whole printed
checkable local-constancy definition. The weak-tracking source interpretation
remains open in the [audit](CHAPTER2_SOURCE_AUDIT.md). This addition belongs to
existing review unit 4, with no new FP assumptions or native changes.

```sh
lake build TrackingCertificates
lake env lean tests/TrackingCertificates.lean
lake env lean tests/PropertyComposition.lean
./check.sh
```

## Coordinate-freezing sufficient rule

The printed p.37 / PDF p.53 image was rechecked. The local-constancy check
holds selected coordinates fixed while quantifying over nearby tuples. The new
`FrozenConstant g v B z` states its neighborhood-form sufficient certificate:
eventually near v, every tuple agreeing with v on flagged coordinates B has
actual result `some z`. This uses real product topology and an explicit defined
value, rather than guessing exceptional equality conventions. We do not claim
this definition alone is an iff translation of the full printed predicate.

`frozen_composeN` proves local constancy of existing strict `composeN` from:
actual child values v and outer value z at x; actual child tuples a(y) nearby;
that same tuple tending to v within S; and eventual equality of each flagged
coordinate to v. Pulling the outer neighborhood back along a and intersecting
the finite flagged-coordinate neighborhoods proves the result. Unflagged
children may vary; requiring all children locally constant is unnecessary.
Neither convergence nor a vacuous outer guard supplies a missing point value.

The projection fixture freezes coordinate 0 at 7 and lets coordinate 1 vary
as y. It applies the actual composition theorem. A negative fixture proves the
identity at zero cannot have this certificate with no frozen coordinates.
Both original continuity-masking controls remain unchanged. Certificate failure
continues to require `sufficient` transport (possible=True), not a false semantic
property. The new result is sufficient and relative to S, not a proof of the
printed composite-to-recursive weak direction for local constancy.
