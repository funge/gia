# Chapter 2: source-numbered proof checklist

This is the maintained Chapter 2 roadmap, beginning with the finite §2.10
milestone. **Chapter 2 is not complete.** The [completion criteria and dependency plan](CHAPTER2_COMPLETION.md) defines the section-by-section exit evidence. A restricted counterpart is not a
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
| §2.11 Interval Function Domains (§§2.11.1–5) | [DomainConstraints](DomainConstraints.lean) proves a finite predicate-level same-parameter conjunction and classification-weakening bridge, reusing universal soundness and affine reciprocal guards; numeric descriptions/demotion remain separate. [PartialEnclosures](PartialEnclosures.lean): `FunctionalBounds`, `DomainBounds`, `Sound`, definite/possible domains, restriction, collapse exclusion. [DomainEvaluator](DomainEvaluator.lean), [GuardedEvaluator](GuardedEvaluator.lean), [SquareRootDomains](SquareRootDomains.lean) provide restricted guards/partial semantics. | General source value/domain description systems and extensions remain open. `Contains` alone proves no actual value exists; bounds may collapse outside a certified domain. Guard failure stays unknown except explicitly proved completeness cases. |
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

## Finite logical and numeric-domain interfaces

The [finite comparison package](FINITE_COMPARISONS.md) and
[domain projections](DOMAIN_PROJECTIONS.md) cover optimistic/pessimistic
projections, exact independent finite comparison images, threshold/nonzero
classifiers and same-witness partial sqrt/division domain bridges. Numeric
re-encoding preserves classifications under explicit whole-image and transport
premises. Touching/equal-singleton, correlation, holes, nonmonotone predicates
and unsafe re-encoding controls are kernel-checked. Source: Tupper §2.7.2
(printed p.24 / PDF p.40) and §2.11 (printed pp.34–36 / PDF pp.50–52).
Exceptional endpoints, general descriptor generation and full family demotion
remain outside this milestone; Chapter 2 is not complete. No native or FP
contract change is made.


## Mathematical representations, bounds and exceptions

The representation unit adds [extended actual-real-image hulls](EXTENDED_IMAGE_HULL.md),
[source-scoped exceptional comparisons](EXCEPTIONAL_COMPARISONS.md) and
[arithmetic](EXCEPTIONAL_ARITHMETIC.md), [literal-infinity controls](EXCEPTIONAL_FAMILIES.md),
[signed divergence correspondence](INFINITY_STREAMS.md),
[integer promotion/demotion](NUMBER_PROMOTION.md), and
[finite-family extremal demotion](DISCRETE_DEMOTION.md).
The independent positive-infinitesimal leaf reuses pinned mathlib.
[Finite interval algebra](INTERVAL_ALGEBRA.md), [nonnegative cut arithmetic](CUT_ARITHMETIC.md),
[rational sequences/digits](SEQUENCE_AND_DIGIT_REPRESENTATIONS.md) and
[canonical continued-fraction conversion](CONTINUED_FRACTION_CONVERSION.md)
record their exact source correspondences and boundary controls.

These are mathematical proofs, not native deployment or a completion of Chapter 2.
Empty actual-real images, infinite bounds, literal infinity tags and lambda are
distinct. Mixed exceptional comparison directions, full source-carrier promotion,
unspecified arithmetic rows and arbitrary infinite coefficient reconstruction
remain open. Later family conversion and property-tracking units are not included.
No floating-point premise or hardware implementation changes.


## Families, sets and domain-compatible demotion

[Family demotion](FAMILY_DEMOTION.md) and its
[general partial-domain rule](GENERAL_FAMILY_DEMOTION.md) preserve shared witnesses
and separate enclosure from classification. Concrete instances cover
[linear equality and its source qualification](LINEAR_FAMILY_EQUALITY.md),
[multiple affine parameters](MULTI_AFFINE_FAMILIES.md),
[quadratic families](QUADRATIC_FAMILIES.md), and the
[finite promotion chain](FINITE_FAMILY_CHAIN.md).
[Interval sets](INTERVAL_SET_DENOTATION.md),
[set-valued extension](INTERVAL_SET_EXTENSION.md),
[coefficient variants](INTERVAL_COEFFICIENT_VARIANTS.md), and
[finite descriptions](FINITE_DESCRIPTIONS_AND_CUTS.md) retain their explicit
representation restrictions. [Descriptor demotion](DESCRIPTOR_DEMOTION.md) proves
a whole-set conversion and preserves external holes and original tags.

These results do not establish a universal finite family syntax, arbitrary bumpy
functions, or the full source exceptional algebra. Inclusion is not exactness;
projected range containment is not pointwise containment at a shared parameter.
Property tracking and expression accuracy remain separate. No native/default
change or new floating-point premise is included; Chapter 2 remains incomplete.


## Partial properties and accuracy: integrated scope

[Partial properties](PARTIAL_PROPERTIES.md), [finite-arity composition](FINITE_PROPERTIES.md)
and [tracking certificates](TRACKING_CERTIFICATES.md) prove exact strict
definedness and sufficient continuity/local-constancy transport on actual shared
tuples. The literal source weak-continuity implication remains refuted by the
constant and square masking controls; sufficient certificates are not silently
substituted for that source claim. Failure of a certificate remains inconclusive.

[Expression streams](EXPRESSION_STREAMS.md) prove eventual success, enclosure and
convergence for the existing finite rational arithmetic evaluator when its limit
has a strict semantic value. Endpoint containment is an additional premise for
a limit-value error certificate. The compiled proof-backed search example rejects
two initial stages and returns a certified interval; it is not a new native FP
backend, a rate bound, or an implementation of arbitrary real inputs.

The [consolidated source audit](CHAPTER2_SOURCE_AUDIT.md) is the current finish-line
map. Full source-carrier/exceptional promotion, the weak-tracking interpretation,
and general finite guard/piece representations remain substantive gaps.
Newer tagged conversion remains separate. Chapter 2 is not declared complete.

## Tagged family conversion preservation

[Tagged conversion](TAGGED_CONVERSION.md) proves exact composition of lifted
real-set converters while retaining literal negative infinity, positive infinity
and lambda separately. Sound empty-preserving converters give arbitrary-predicate
classification refinement and exact represented definedness bits. The real-hull
then integer-hull instance discharges these premises with existing proofs.
This is a derived semantic preservation theorem, not the full source F-to-R*
promotion, an exceptional operation table, or a native implementation. Those
concrete carrier/operation gaps remain in the [source audit](CHAPTER2_SOURCE_AUDIT.md).

## Literal finite-format enclosure

[Finite formats](FINITE_FORMAT.md) proves exact representation of the §2.5
printed p.18 coefficient formula for arbitrary radix at least two, positive
precision and ordered exponent bounds, with least finite in-range directed
enclosure. Its Word bridge requires separate format membership. The adjacent
digit presentation and IEEE identification remain open; no new FP premise or
implementation is introduced, and Chapter 2 remains incomplete.

## Coefficient/digit distinction

[Format digits](FORMAT_DIGITS.md) checks the §2.5 printed pp.18–19 displays:
exact digit-list correspondence, normalized magnitude bounds, literal
nonnegative reindexing and a minimum-exponent obstruction. A checked decimal
counterexample rules out unconditional equality of the displays. An explicitly
labeled external-sign / `b^A` coefficient repair is proved; the original model
is unchanged. Authorial intent, full normalization and IEEE identification remain
open. This refines the earlier “digit correspondence open” entry, not Chapter 2
completion or a new FP assumption.

## Repaired binary64 value correspondence

[Binary64 format bridge](BINARY64_FORMAT.md) proves the full iff between the
repaired `(2,53,-1022,1023)` family and successful finite `Binary64.decode`
values, including normal/subnormal cases and both signed zeros. Bounded exact
normalization and raw-word packing discharge the converse, and identify the
existing mathematical demotion target. This closes the repaired-family bridge
previously deferred above; the literal printed coefficient model is unchanged.
No native transport, exceptional rounding, new FP premise or chapter-completion
claim follows.

## Endpoint certificates and optimality

[Endpoint optimality](ENDPOINT_OPTIMALITY.md) proves that a sound finite decoded
Word certificate equals the least repaired-binary64 hull of a nonempty actual
image iff its endpoints are extremal representable bounds. The existing affine
endpoint checker supplies inequalities, not this extra property; a checked
accepted-but-loose example demonstrates the distinction. Closed intervals and
same-parameter partial families inherit the correspondence, preserving empty
fibers. No native rounding, affine-interior optimality or new FP premise follows.

## Finite guarded piece compilation

[Finite guarded pieces](FINITE_GUARD_PIECES.md) supplies a derived restricted
subclass for §§2.13–2.14: rational affine constraints with strict/closed
boundaries, exact union/intersection compilation to finite conjunction pieces,
and an exact rational membership test. It reuses existential piece denotation
and keeps the same parameter/value witness, external restrictions and empty
fibers. This closes a concrete finite-code gap beyond point tables; it is not
a source-prescribed grammar, arbitrary-function representation, automatic
demotion or a full open/exceptional endpoint model. No FP assumption changes.

## Fixed coefficient witnesses and heterogeneous decoding

[Coefficient witnesses](COEFFICIENT_WITNESSES.md) proves exact conversion of
admissible heterogeneous code pairs into real coefficient pairs, retaining one
witness across uses and any joint pair constraint. With 0 and 1 in the parameter
domain, recovery is exactly `(f 0, f 1-f 0)` plus the affine identity. A mixed
integer/rational instance and a strict marginal-versus-joint counterexample are
checked. The existing pointwise coefficient theorem remains unchanged; §2.14's
equality notation alone does not settle persistence of real choices. No new FP
premise or general heterogeneous exceptional endpoint claim is made.

### Residual §§2.13–2.14 work, classified

| Kind | Residual item | Current boundary / next evidence |
| --- | --- | --- |
| Proof task | Mixed endpoint carriers and boundary types | Finite rational strict/closed bands are compiled exactly; total real coefficient maps now preserve joint witnesses. The subsequent mixed-endpoint milestone closes a concrete integer/rational-to-real conversion with exact open/closed and empty cases; arbitrary real coefficient encodings and the general variant remain open. Infinite bounds and literal exceptional values must stay separate. |
| Proof task | Hansen's full stated multi-parameter coefficient variant | Finite closed-coefficient pointwise denotation, endpoint attainment and shared-use correspondence are now checked in HansenCoefficients. Unbounded sets of finite real coefficients now have the exact convex-image and boundary correspondence in HansenRealSets. Literal exceptional coefficient arithmetic and the full system arithmetic/demotion remain open. |
| Source/specification ambiguity | Persistent choices for repeated interval descriptions | Equality of descriptions does not alone determine equality of chosen real witnesses. Both models now have exact mathematics and a strict separating example; do not mark one as the author's intended convention without evidence. |
| Source/specification boundary | Finite guards and perfect demotion | The printed infinite point construction and finite/unmanageable-description discussion do not supply a general finite input grammar or generation algorithm. The chosen rational affine grammar is a restricted result, not a resolution of that omission. |
| Broader research | General finite realization, optimal demotion and bumpy classification | No universal finite description algorithm, minimal-piece procedure, or all-function classification follows. Specify a source-backed family and representability constraints before treating any such task as a bounded proof obligation. |

Chapter 2 remains incomplete. Beyond these rows, the explicit literal/repaired
format distinction and §2.12 weak/strong tracking interpretation still require
source-level decisions; adding finite examples does not resolve them. The mixed-endpoint milestone below addresses that bounded opportunity without
choosing a persistent-witness convention for the source. The finite Hansen correspondence below now closes the fixed-vector coefficient
case. The next source-facing task should address a specified arithmetic or
demotion operation on that family, with its joint witnesses and exceptional
carrier restrictions made explicit, rather than repeat pointwise enclosure.

## Mixed affine endpoints and boundary flags

[Mixed endpoints](MIXED_ENDPOINTS.md) proves an exact concrete conversion from
integer/rational lower coefficients and rational/integer upper coefficients to
the existing guarded rational pieces. It preserves open/closed flags, guards,
empty fibers and one band/coefficient witness across uses. A full nonemptiness
criterion distinguishes strict and closed equal endpoints. This closes the
concrete finite mixed-carrier task from the preceding checklist; irrational,
extended/undefined carriers and the full Hansen variant remain separate. The
flags and persistent-choice interpretation are explicit model conventions, not
claims inferred from §2.14. No new FP assumptions or chapter-completion claim.

## Finite Hansen coefficient correspondence

[Finite Hansen coefficients](HANSEN_COEFFICIENTS.md) establishes exact fixed-vector
denotation and attained endpoints for finite closed rational coefficient intervals,
including the printed §2.14 two-point parameter sets. A shared coefficient vector
is retained across repeated uses. Pointwise tightness does not imply a convex
projected image or joint attainment of pointwise extrema. Exceptional/unbounded
carriers and the full system's arithmetic/demotion remain open; Chapter 2 is not complete.

## Possibly unbounded finite-real Hansen coefficients

[Coefficient-set correspondence](HANSEN_REAL_SETS.md) now covers arbitrary sets
of finite real coefficients, strict empty-tuple behavior and zero weights. For
convex coefficient sets it proves exact open-interior membership and a precise
finite-boundary attainment criterion; the existing extended hull is least, but
need not equal the image. Same-parameter demotion and tag-preserving conversion
reuse existing results. Literal infinite/λ coefficient arithmetic and whole-system
operations remain open. These are derived set-model results, not extra printed
Hansen conventions or new IEEE assumptions.

## Uniform §2.5 separation and repaired normalization

[Format normalization](FORMAT_NORMALIZATION.md) proves that `b^M` separates the
printed unsigned digit display from the literal coefficient format for every
`b ≥ 2`, `A ≥ 1`, `m ≤ M`. It also proves equality of the separately labeled
unrestricted repaired and normal-or-minimum value sets at arbitrary radix.
This closes the value-set normalization proof gap, not authorial intent,
exceptional rounding or hardware semantics. The literal definition is unchanged.
