# Chapter 2: source-numbered proof checklist

This is the maintained Chapter 2 roadmap, beginning with the finite §2.10
milestone. **Chapter 2 is not complete.** A restricted counterpart is not a
formalization of the entire source section. The project proves GIA foundations;
graphing remains one application. See the [concordance](THESIS_CONCORDANCE.md)
for Chapter 3 and later consumers, and the [FP roadmap](FLOATING_POINT_ROADMAP.md)
for the implementation trust boundary.

Source: Jeffrey Allen Tupper, *Graphing Equations with Generalized Interval
Arithmetic* (1996), [contents](https://www.dgp.toronto.edu/~mooncake/thesis/node1.html)
and [original PDF](https://www.dgp.toronto.edu/~mooncake/thesis.pdf).
For the exact image-hull milestone, §§2.7.3–2.8 were also visually checked on
printed pp. 24–26 (PDF pp. 40–42); see [scope](EXACT_IMAGE_HULL.md).
Section headings were cross-checked against the available transcription and
existing source records. For this milestone, §2.10 was additionally read visually
on printed pp. 32–33 (PDF pp. 48–49) in the existing repository source copy;
no source copies are added or needed by the build. The HTML §2.10 fetch failed
in this session, so that link is a citation, not a fresh accessibility claim.
The strict-comparison milestone additionally checked §§2.7.2 and 2.9.2 visually
on printed pp.24 and 27 (PDF pp.40 and 43); see [scope](STRICT_COMPARISON.md).
The Boolean-composition tranche rechecked §2.9.2 on printed p.27 / PDF p.43.
The author's linked contents also confirms §§2.15.1–8 (the local transcription
only labels the first three); this numbering correction adds no proof coverage.
Other rows inventory current code and carry forward the concordance's source
qualifications; they are not claims of a fresh line-by-line proof audit of each
section. Ambiguous formulas must be checked against the PDF before implementation.

Use the remaining-work column as the checklist; no row below is marked complete.
Update the relevant row with each source-led milestone rather than duplicating
historical test counts here.

| Source section | Current evidence / restricted coverage | Remaining work and precise boundary |
| --- | --- | --- |
| §2.1 Integers | Lean/mathlib `ℤ`, arithmetic/order; [IntegerResidue](IntegerResidue.lean) and [ResidueInference](ResidueInference.lean) are applications. | Map required source operations/order to library declarations as used; do not rebuild integers or count residue applications as a proof of the section. |
| §2.2 Rational Numbers | mathlib `ℚ`; [Intervals](Intervals.lean), [LinearIntervals](LinearIntervals.lean) use exact rational endpoints/coefficients. | Library foundation, not a substitute for hardware arithmetic; no independent source algebra reconstruction is claimed. |
| §2.3 Real Numbers | mathlib `ℝ`, ordered-field reasoning and analysis underlie enclosure proofs. | Record imported foundations as dependencies; not a new construction of the reals. |
| §2.4 Complex Numbers | mathlib has complex numbers; current GIA bounds target real values. | Complex interval representations, order conventions and arithmetic are not implemented. Availability in mathlib is not project coverage. |
| §2.5 Floating Point (§§2.5.1–4 infinity, NAN, rounding, algebra) | [Binary64](Binary64.lean) decodes finite raw words exactly to rationals, rejects nonfinite/out-of-range words, identifies both zeros with real zero. [HardwareAddition](HardwareAddition.lean), [HardwareSubtraction](HardwareSubtraction.lean), [HardwareMultiplication](HardwareMultiplication.lean), [HardwareDivision](HardwareDivision.lean) prove conditional directed-operation enclosure. | Full source rounding/order/exception algebra, closest-representable rounding, signed-zero behavior and native Float/raw-word refinement remain separate. Rejecting infinities/NaNs does not formalize their source arithmetic. Existing adapter/compiler/hardware contracts remain trusted; no new FP assumptions here. |
| §2.6 Extended Real Numbers (§§2.6.1–3) | Partial real relations avoid totalized division; split rays can describe unbounded sets without extended endpoints. | Tupper's extended-real, hyperreal, conversion and infinity conventions are not a project number system. Do not equate absent decoded values with a verified infinity convention. |
| §2.7 Interval Arithmetic (§§2.7.1–5) | [IntervalOps](IntervalOps.lean), [Evaluator](Evaluator.lean): finite real containment, rational arithmetic enclosure and restricted compositional evaluation. [StrictComparison](StrictComparison.lean) proves the exact Boolean image for strict comparison of independent finite operands. [ExactImageHull](ExactImageHull.lean) adds nonempty bounded actual-image inclusion, least closed hull and refinement; independent interval addition agrees with that hull and successful outward results contain it. | General n-ary computational extension/demotion, other source interval relations and algebra, generalized coefficient systems remain open. Mere enclosure does not imply exact image membership or leastness. |
| §2.8 Real Interval Arithmetic | Nonempty bounded real output sets now have a proved least closed hull in [ExactImageHull](ExactImageHull.lean), without a general attainment claim. Finite endpoint inequalities and rational instances; [EndpointChords](EndpointChords.lean) and [TangentBounds](TangentBounds.lean) provide later-chapter restricted bounds. | Empty/unbounded output semantics, general demotion algorithms, extended endpoints and full order/algebra remain open. The hull theorem is a specification, not an arbitrary extrema algorithm. |
| §2.9 Generalized Interval Arithmetic (§§2.9.1–8) | [BooleanComposition](BooleanComposition.lean) gives exact independent not/and/or images on the existing finite Truth type, subset soundness for joint/common-witness inputs, finite table algebra and strict correlation controls; see [scope](BOOLEAN_COMPOSITION.md). [StrictComparison](StrictComparison.lean) maps F/TF/T to the three nonempty Boolean intervals, with inclusion as information refinement; only independent finite strict comparison is implemented. [LinearIntervals](LinearIntervals.lean): one shared parameter, coefficient/endpoint correspondence, pointwise noncollapse, constant embedding; [LinearMultiplication](LinearMultiplication.lean): quadratic remainder enclosure. [PartialEnclosures](PartialEnclosures.lean) permits arbitrary parameter types for functional bounds; [HardwareAffine](HardwareAffine.lean) retains shared endpoint witnesses. | No full unification/family calculus or recursive three-valued system (projections and partial-expression integration remain deferred), general quadratic-bound representation, multidimensional affine coefficient family, or symbolic interval system. Polynomial expression syntax and a quadratic product theorem are not the full quadratic interval representation. Arbitrary-parameter semantic predicates are not executable multi-parameter arithmetic. |
| §2.10 Generalized Floating Point Interval Arithmetic | **Current finite tranche:** [FiniteAffineDemotion](FiniteAffineDemotion.lean), documented [below](FINITE_AFFINE_DEMOTION.md): certify four supplied binary64 endpoint words; reuse `linear_bridge`; prove pointwise enclosure/noncollapse; conditionally evaluate stored bounds outward at one shared parameter. | Endpoint-basis finite specialization only. No arbitrary-family/extended-real/multiple-parameter demotion, source p,q coefficient-rounding implementation, automatic converter, exact rounding, optimality, ULP bound or native Float/Word proof. Ideal-to-stored certification and stored-to-evaluated enclosure are distinct. |
| §2.11 Interval Function Domains (§§2.11.1–5) | [PartialEnclosures](PartialEnclosures.lean): `FunctionalBounds`, `DomainBounds`, `Sound`, definite/possible domains, restriction, collapse exclusion. [DomainEvaluator](DomainEvaluator.lean), [GuardedEvaluator](GuardedEvaluator.lean), [SquareRootDomains](SquareRootDomains.lean) provide restricted guards/partial semantics. | General source value/domain description systems and extensions remain open. `Contains` alone proves no actual value exists; bounds may collapse outside a certified domain. Guard failure stays unknown except explicitly proved completeness cases. |
| §2.12 Property Tracking (§§2.12.1–3) | [SemanticContinuity](SemanticContinuity.lean), [ConditionalContinuity](ConditionalContinuity.lean), [CellContinuity](CellContinuity.lean): conditional continuity/gluing. [PropertyComposition control](tests/PropertyComposition.lean) records source-specialization counterexamples. | General recursive weak/strong property tracking is unresolved; see the concordance's §2.12 source tension before adopting a generic API. Do not silently reverse the printed implication or conflate sufficient structural certificates with semantic equivalence. |
| §2.13 Interval Sets (§§2.13.1–2) | [FiniteLinearCovers](FiniteLinearCovers.lean), [CoverArithmetic](CoverArithmetic.lean): finite union coverage and operations; [SplitQuotient](SplitQuotient.lean): restricted exact reciprocal image and same-valuation expression enclosure. | General set extensions/demotion, perfect or infinite representations and source bumpy-function classification remain open. Split quotient is not full domain/continuity flag tracking; arbitrary expression enclosure need not be exact image. |
| §2.14 Variants | `LinearInterval.exact` is an equal-bound instance; `HardwareAffine.Form` stores interval-valued endpoint uncertainty. | General mixed coefficient systems, source equal-bound variants and Hansen-style multi-parameter family need separate correspondence proofs. Current instances do not establish the full section. |
| §2.15 Real Representations (§§2.15.1–8) | Uses mathlib's real foundations and exact rationals for certificates. | The eight-part representation survey is not separately formalized; no verified alternative real-computation backend is claimed. |

## Imported foundations, not rebuilt number systems

The finite layer uses mathlib's integers/rationals/reals, their coercions,
`+`, `-`, `*`, `/`, `≤` and `<`. For example, `affine_order` in
[LinearIntervals](LinearIntervals.lean) uses `add_le_add` and
`mul_le_mul_of_nonneg_left`; endpoint certification uses order transitivity
and exact rational-to-real coercion. Polynomial identities use the existing
`ring`/`norm_num` infrastructure. Real continuity and convexity in later
modules are library dependencies, not newly claimed Chapter 2 constructions.

## Next source-led obligations

1. Review the finite §2.10 certificate/evaluation interface before extending it.
2. Specify a finite §2.7/§2.9 family inclusion and demotion relation if needed by
   subsequent operations; reuse the existing pointwise semantics and avoid
   asserting leastness from containment alone.
3. Address extended-real and multi-parameter representation choices explicitly
   before claiming the general Chapter 2 system. Keep native refinement and
   exceptional floating-point behavior as separate, approved work.
