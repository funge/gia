# Finite constant, affine and quadratic promotion/demotion

This closes a concrete missing link in the existing Chapter 2 family proofs.
The earlier modules already prove constant embedding, affine inclusion criteria,
affine-to-quadratic embedding, quadratic arithmetic and constant enclosures.
They did not provide a demoter for a general finite quadratic interval to affine
bounds: `product_chord_demotion` handled only products of two affine forms.

[FiniteFamilyChain](FiniteFamilyChain.lean) now gives the complete one-parameter
finite rational chain, reusing those proofs rather than postulating inclusion.

## Source and exact scope

Tupper §2.9.4 (printed p.30 / PDF p.46) gives the injective constant-to-linear
mapping with zero slope. §2.9.5 on the same page specifies quadratic bounds by
three coefficients each and requires the bounds to be well-defined. §2.9.3
(pp.29–30) requires outward functional demotion and does not provide a universally
best affine demotion. These statements and the exceptional example were checked
visually in the original PDF: [source p.30](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=46).

Our converter is a derived finite mathematical construction satisfying that
inclusion obligation, not a transcription of a Chapter 2 conversion algorithm.
For p+qt+rt² it adds the exact affine p+qt to the already certified product bounds
for t·(rt). Equivalently its affine bounds are:

- lower: p+(q+r)t−max(r,0)/4;
- upper: p+(q+r)t−min(r,0)/4.

The existing bubble/chord proof supplies the error bound on 0≤t≤1. No new
curvature, rounding, hardware or extremality assumption is added. For an interval
with different lower and upper quadratic forms, the converter uses the lower
form's lower affine bound and the upper form's upper affine bound. Its endpoint
order is proved from the supplied valid quadratic interval's order and the
concrete form bounds; it is not a new caller-supplied inclusion premise.

This matches §2.9.5's one-parameter family with finite rational coefficients.
Existing arbitrary-dimensional affine embeddings remain available; this is not a
new multivariate quadratic optimizer or a demoter for all extended-real functions.

## Deductive chain

- `promote_contains` composes the existing endpoint-basis and polynomial-basis
  embeddings, preserving every fiber at the same t. `constant_chain` specializes
  this to ordinary QInterval membership.
- `formBounds_encloses` proves the supplied coefficient construction bounds every
  actual form value. `demote_encloses` then preserves every admitted interval
  value, including non-singleton fibers. `chain_encloses` projects the result
  through the existing affine constant hull.
- `round_trip` proves demote(promote I)=I for every finite affine interval;
  `promote_injective` follows. `constant_hull_round_trip` also recovers the exact
  original constant interval. Thus zero-curvature promotion/demotion is exact,
  whereas general quadratic demotion is an enclosure.
- `demoted_inclusion_iff` reduces inclusion of the constructed affine results to
  four concrete rational endpoint comparisons using the existing exact criterion.
- `partial_chain` preserves the exact domain classification of the actual
  relation `Cube t ∧ P t w ∧ I.Contains t z`, with the same admitted witness w.
  Both the affine and constant results are sound; no marginal projections or
  independent replacement witnesses are introduced. The arbitrary predicate P
  is a semantic partial domain, not a claim to have generated a decidable guard.

No theorem says every value admitted by a demotion is attained. No general
operator homomorphism is inferred from representation equality: existing finite
constant arithmetic identities remain their own proofs.

## Strict and failure controls

[Fixtures](tests/FiniteFamilyChain.lean) exercise the actual converter:

- t(1−t) produces constant hull [0,1/4], excluding 1/2, while the previous coarse
  quadratic hull [−1,1] admits 1/2. The midpoint value 1/4 is retained.
- t²'s demoted fiber at t=0 admits −1/4, which the exact quadratic fiber excludes.
  Its projected affine hull also admits −1/4 while the direct quadratic hull
  [0,1] excludes it. Neither demotion is claimed universally better.
- No exact affine function equals t² throughout [0,1], proved using three points.
- A non-singleton interval [t²,t²+1/2] retains every t²+δ for 0≤δ≤1/2.
- The original product shares t. Evaluating its two factors at different t values
  gives a different result and is explicitly not the product semantics.
- A hole at t=1/2 remains a hole even though the demoted numeric fiber admits 1/4.
  The same exact domain description is retained by both stages.

## Concrete exceptional cases not covered by finite promotion

These are actual source/model boundaries, not hypothetical feature requests:

1. The unbounded constant [−∞,+∞] cannot be encoded by finite rational
   endpoints. `no_finite_infinity` checks the finite-to-EReal distinction, and
   `no_finite_unbounded_constant` proves no QInterval contains all real values.
   Its promotion requires extended bounds; the finite round trip cannot supply it.
2. The source explicitly rejects the bound ∞−∞α at α=1/2 (p.30). It cannot be
   formed in the rational coefficient carrier. Finite coefficient algebra cannot
   justify its cancellation or totality; extending this converter requires the
   source exceptional evaluation/validity rules. We do not invent the missing
   exceptional arithmetic rows or turn unmodeled observations into λ.
3. λ is not a real payload or an EReal bound. Existing source comparison semantics
   makes both strict outside tests false for λ; the reused fixture shows why the
   finite negated-outside membership test would wrongly admit it. Its `bound`
   translation is absent, so the real-valued fiber theorem cannot be applied.

This adds no exception carrier or IEEE interpretation. The mathematical domain
hole is preserved independently of these exceptional-value questions. The source
ledger now marks the finite quadratic-to-affine construction checked; full
exceptional coefficient validity and general nonlinear demotion remain open.
Keep this entire chain in existing family review unit 3. Nothing is published.
