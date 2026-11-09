# Sound finite-cover coalescing

Tupper's [interval-set inclusion and extension (§2.13.1)](https://www.dgp.toronto.edu/~mooncake/thesis/node57.html)
notes that highly precise descriptions can become unmanageably large. This
motivates a bounded, approximate representation policy. The policy here is a
small implementation choice justified by an inclusion proof; it is not claimed
to reproduce a thesis optimization algorithm or an optimal demotion.

`FiniteLinearCover.IncludedIn` expresses inclusion of represented values at each
shared unit parameter. It compares ranges only, not domains. Reflexivity,
transitivity, and transport of `Covers` and `SoundOn` are proved. Domain transport
keeps the same definite and possible predicates and the same actual relation;
it changes only the range enclosure. `IncludedIn` is a semantic proposition,
not an executable inclusion test.

`singleton_soundOn_iff` identifies singleton-cover soundness with the existing
linear partial-enclosure interface exactly. This provides a proved bridge back
to scalar consumers rather than creating another domain representation.

`joinFrom` recursively joins a nonempty list with the existing linear join.
`coalesce` leaves an empty cover empty and replaces a nonempty cover with one
joined linear interval. Every represented value remains enclosed, and output
length is at most one. Joining uses affine endpoint minima/maxima, retaining
sloping bounds rather than forcing a constant hull.

`limit n C` has an explicit policy:

- If C has at most n components, return it unchanged.
- Otherwise, if n is positive, return the fully coalesced cover.
- Otherwise return `none` (unknown); do not replace a nonempty cover by empty.

Successful output is proved to include the input range and have length at most
n. Any positive limit succeeds; an empty cover also succeeds at limit zero.
Success alone supplies no existence or absence claim; a semantic contract is
still required. The same `SoundOn` contract transfers to successful output. The limit is a
maximum, not a target: three components with limit two become one. No subset
selection, deduplication, normalization, or optimal precision claim is made.
This operation is opt-in and does not change either interpreter's default.

The implementation is postprocessing. It traverses an already constructed list
and is not a bound on evaluation time, peak memory, recursion depth, intermediate
cover sizes, or arithmetic-tree expansion. Enforcing a runtime resource budget
would need a separate evaluator policy and proof; this milestone makes no such
claim.

The examples compose conditional interpretation with limit one and retain its
punctured coordinate-domain contract. Actual values remain guaranteed at a
definite point, and the excluded parameter remains absent. The singleton result
also satisfies the original scalar partial-enclosure contract.

Precision loss is tested explicitly: a joined cover represents zero at a point
where the actual jump has no zero, and the reverse range inclusion is refuted.
Componentwise reciprocal succeeds before coalescing and becomes unknown after
it. This is safe loss of information, not a change to actual expression values.
Zero-limit rejection and empty-limit success are checked separately. An
independent three-component example computes the exact sloping output bounds.
The earlier two-slope conditional's actual-root certificate still succeeds
using the coalesced contract and newly checked endpoint signs.

No FP assumptions, new expression syntax, continuity inference, maximal-domain
analysis, application integration, or hosted CI changes are introduced. The
unchanged axiom audit covers every public theorem and the new modules.
