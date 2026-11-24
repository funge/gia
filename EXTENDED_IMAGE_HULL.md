# Extended bounds for actual real output sets

Tupper §2.7.4 (printed p.25 / [PDF p.41](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=41))
defines interval extension using the infimum and supremum of actual outputs,
allowing an infinite bound when no finite bound exists. §2.8 uses extended real
endpoints. The transcription was read and the original §2.7.4 page visually
checked. This module proves the bound-only correspondence for arbitrary sets of
**real** outputs. It does not formalize exceptional arithmetic or native infinity.

## Representation and exact claims

[ExtendedImageHull](ExtendedImageHull.lean) embeds S : Set Real into pinned
mathlib EReal, an ordered complete carrier. Its lower/upper bounds are the
infimum/supremum of that embedded set. Its hull consists of real x between those
bounds. No EReal arithmetic is used.

* `sound` encloses S without nonempty/bounded premises.
* `endpoint_least` proves any other pair of extended bounds enclosing S lies
  outside the canonical pair. `least` and `enclosure_iff` express leastness among
  sets of real members of extended closed intervals, including reversed bounds.
* `mono`, `interval_fixed` and `idempotent` express refinement and hull closure.
* The **empty image** has canonical bounds (+infinity,−infinity) and empty real
  membership. This reversed pair is explicit, not a normal nonempty QInterval,
  a NaN, lambda, or an unavailable computation. `ordered_iff` and `nonempty_iff`
  hold for these canonical hulls. They are not a claim that every ordered pair
  of extended bounds admits a real value: (+infinity,+infinity) admits none.
* `lower_finite` uses only nonemptiness and a finite lower bound; `upper_finite`
  is dual. `finite_agreement` identifies the hull with existing ExactImageHull
  on nonempty bounded S. The endpoints need not be attained.
* `lower_unbounded` and `upper_unbounded` identify the appropriate infinite
  bound when a finite bound does not exist. Infinity is a bound, not a real
  value produced by the modeled operation.
* `relation_enclosure` takes an actual relation image with one admissible input
  witness. It needs neither totality nor Cartesian independence. A missing
  semantic value contributes nothing to the image; it is not replaced by a
  totalized division value.

[Fixtures](tests/ExtendedImageHull.lean) cover the empty image, the whole real
line, both one-sided closed rays, a bounded interval, the open interval (0,1)
and its unattained hull endpoint, a pole-only empty image, a shared t+(-t)
image and a guarded reciprocal relation. A control demonstrates why the old
finite hull's nonempty premise cannot be dropped: its empty-set expression
contains zero, while the extended canonical empty hull does not.

## Separate hyperreal leaf

[HyperrealInfinitesimal](HyperrealInfinitesimal.lean) imports only pinned
`Mathlib.Data.Real.Hyperreal` and uses `epsilon_pos`, `epsilon_lt_pos` and
`coe_lt_coe`. It proves the source §2.6.1 statement (printed p.21 / PDF p.37):
there is a positive hyperreal smaller than every positive embedded real. It also
proves this epsilon is not the image of any real. The source inequality was
visually checked in the original PDF during the preceding design review.
[Its fixtures](tests/HyperrealInfinitesimal.lean) check the half-unit bound and
nonidentity with real zero. This is a source-to-library proof, not a new model,
signed-zero interpretation, IEEE bridge or general transfer theorem. It is
independent of the hull and all GIA arithmetic modules.

## Boundaries and integration

This representation unit follows the merged finite comparison/domain package.
ExtendedImageHull imports only ExactImageHull and mathlib; it has no mathematical
dependency on finite comparison. The exceptional comparison/arithmetic subset
and mathematical promotion results are documented separately in this unit.

This closes the empty/unbounded **actual-real-image bound** gap, not all of
§2.6/§2.8. The scoped exceptional tables and promotion results below do not supply the
full source family universe or the complete interval calculus. EReal equality and ordering here are mathematical bound relations,
not Tupper's exceptional floating-point comparisons or IEEE instructions.
There is no executable evaluator, rounding claim, new FP assumption, native
change or output-attainment claim.

```sh
lake build ExtendedImageHull HyperrealInfinitesimal
lake env lean tests/ExtendedImageHull.lean
lake env lean tests/HyperrealInfinitesimal.lean
./check.sh
```

See [design note](EXCEPTIONAL_VALUES_DESIGN.md), [completion ledger](CHAPTER2_COMPLETION.md),
[concordance](THESIS_CONCORDANCE.md) and [validation](VALIDATION.md).
