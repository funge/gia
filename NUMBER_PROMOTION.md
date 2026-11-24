# Mathematical promotion and extended-integer demotion

[NumberPromotion.lean](NumberPromotion.lean) specializes Tupper §2.9.1,
printed pp.26–27 / PDF pp.42–43: the explicitly supplied family
`Z* = Z ∪ {-∞,+∞}` and outward demotion of the infimum/supremum of
actual outputs. Source: [original thesis PDF](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=42).
The original page images were checked; this is not an inference from a damaged
Markdown formula. §2.6.2's distinction between promotion and demotion motivates
the exact embedding lemmas, without identifying rounded arithmetic with real arithmetic.

`IntegerBound` recognizes precisely these endpoint meanings in EReal.
`down` and `up` preserve infinite endpoints and use mathematical floor/ceiling
on finite reals. `down_greatest` and `up_least` prove their optimality from
mathlib's floor laws, rather than assuming a rounding contract. `sound` and
`least` then prove that their application to the existing actual-image bounds
is the least closed extended-integer enclosure. `finite_formula` identifies
its finite nonempty bounded specialization. Empty images retain top/bottom
and no members; unbounded images need no boundedness premise.

`relation_sound` uses an actual witness in a supplied domain and relation.
No totality, Cartesian independence or value at an undefined point is inferred.
The output enclosure can contain unattained values. In particular the image
{1/2} demotes to [0,1], admitting zero; exact integer endpoints are fixed.

Exact integer and rational promotions into `ExceptionalComparisons.Value.finite`
are injective, and integer→rational→real agrees with integer→real.
`integer_bound_correspondence` agrees with the existing bound interpretation.
The existing negative/positive infinity tags map to bottom/top, while lambda
has no bound meaning. That mapping does not equate exceptional numerical
comparison with EReal order (nor with Lean equality).

## Representation map and limits

| Source family | Existing meaning / coverage | Remaining distinction |
| --- | --- | --- |
| Integers, rationals, reals | Exact casts into finite real payloads | No rounded-arithmetic homomorphism claim |
| Extended integer endpoints | IntegerBound, proved floor/ceil demotion | Mathematical, noncomputable cold proof layer |
| Extended real bounds | ExtendedImageHull; infinities bound real outputs | Not attained real infinities or source arithmetic |
| Undefined lambda | Value.undefined, bound = none | No integer-bound demotion of lambda |
| Finite binary64 | Existing Binary64.decode exact rational; conditional native contracts | No new converter or native/Word bridge |
| Hyperreals | Existing independent infinitesimal leaf | No general promotion/standard-part or transfer API |
| Boolean/affine/set families | Existing separate family modules | No universal cross-family conversion implementation |

This closes the concrete extended-integer endpoint instance of §2.9.1, not the
full source family universe or IEEE promotion/demotion. There is no C/native
change, runtime rational fallback, new axiom or floating-point assumption.

Run `./check.sh`; [tests/NumberPromotion.lean](tests/NumberPromotion.lean)
covers signs, fractional widening, zero/integer and infinite boundaries,
empty/universal images, embedding coherence and the undefined bound tag.
