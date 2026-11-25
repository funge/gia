# Chapter 2: source-to-Lean closeout audit

Current audit after #67, checked against **all printed pp.13–43 / PDF pp.29–59**
of [Tupper’s 1996 thesis](https://www.dgp.toronto.edu/~mooncake/thesis.pdf),
including every numbered subsection below. The repository transcription was used
only as an index; formulas and ambiguities were read from page images. This
replaces the stale initial-milestone table. Historical proof receipts remain in
[the source audit](CHAPTER2_SOURCE_AUDIT.md), [validation](VALIDATION.md), and
individual scope documents. The [closeout matrix](CHAPTER2_CLOSEOUT.md) is the
short summary; it must not turn each imaginable generalization into a new source
obligation.

**Status keys:** E = exact mathematical result at the named scope; B = imported
mathematical foundation; R = deliberately restricted counterpart / remaining
correspondence proof; C = checked contradiction under the specified reading;
U = genuinely unspecified semantics/algorithm or unresolved interpretation;
D = description, cited background, or optional research beyond an explicit
Chapter 2 theorem. Mixed labels are intentional. A set denotation theorem is not
an executable converter. No row claims native, C, or IEEE implementation proof.
The mathlib pin is `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

## Every section and subsection

The Lean anchors name declarations within the linked module; scope documents
provide the longer hypotheses. Printed page anchors distinguish source evidence
from our derived constructions. An E beside a row does not erase its R/U part.

| Section / printed page | Explicit claim or definition | Status | Lean anchor | Exact residual / classification |
| --- | --- | --- | --- | --- |
| §2.1 ([13–15](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=29)) | Integers; operation graphs, partiality, rings/order | **B/E** | [NumericFoundations](NumericFoundations.lean): `integer_rational_embedding; integer_division_not_closed; integer_alternative_distributivity_fails` | Int and ordered-ring laws are imported. Generic function notation is a definition, not a requested new type theory. |
| §2.2 ([15–16](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=31)) | Rational promotion and lack of a total square root | **B/E** | [NumericFoundations](NumericFoundations.lean): `integer_rational_injective; no_total_rational_root` | Nonzero denominator is essential. Earlier audit “unmapped root/embedding” entries are superseded. |
| §2.3 ([17](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=33)) | Real sequence representation and partial real root | **B/E** | [NumericFoundations](NumericFoundations.lean): `rational_sequence_exists; real_root_domain` | Real construction and field laws use pinned mathlib; bare totalized Real.sqrt is not the source partial root. |
| §2.4 ([17–18](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=33)) | Complex embedding, total root, no compatible field order | **B/E/D** | [NumericFoundations](NumericFoundations.lean): `real_complex_embedding; complex_root_total; no_complex_ordered_ring` | Doubling/quaternions and computing resources are a cited survey, not a complex interval implementation specification. |
| §2.5 ([18–19](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=34)) | Coefficient and digit presentations of a finite format | **E/C** | [FormatNormalization](FormatNormalization.lean): `upper_digit_witness; repaired_iff_normal_or_minimum` | The printed displays have different value sets. Repaired binary64 iff is Binary64Format.repaired_iff_decode, not a proof of the literal IEEE identification. |
| §2.5.1 ([19](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=35)) | Signed infinity tags and specified addition/comparison rows | **R/U** | [ExceptionalComparisons](ExceptionalComparisons.lean): `same_sign_infinities; add_positive_infinity_cases` | Same-sign numerical equality differs from structural equality. Full mixed/undefined-input arithmetic is not determined by these rows; the quantified addition example needs an explicit reading of its exceptional guard. |
| §2.5.2 ([19](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=35)) | Lambda, negative-root example and unordered comparisons | **E/U** | [ExceptionalComparisons](ExceptionalComparisons.lean): `undefined_left; undefined_right; sqrt_negative` | The five named comparisons exclude numerical not-equal; sentinel definedness tests are separate. Missing operation cases must not be supplied from IEEE. |
| §2.5.3 ([20](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=36)) | Directed extrema, nearest rounding and decimal examples | **E/C/U** | [SourceRoundedAlgebra](SourceRoundedAlgebra.lean): `decimal_literal; decimal_repaired; literal_up_not_printed` | NearestMinimizers.exists_iff/tie_iff give selection-free facts. Tie choice, exceptional overflow and the illustrative 40-ULP sine implementation are not specified algorithms or proved native behavior. |
| §2.5.4 ([21](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=37)) | Rounded algebra, identities, failures of associativity/distributivity | **E/C/R** | [SourceRoundedAlgebra](SourceRoundedAlgebra.lean): `multiplication_nonassoc; mixed_distributivity; printed_reassociation` | DirectedOperationAlgebra proves finite in-range identities. Printed decimal reassociation rows require correction; universal exceptional identity/inverse laws are not inferred from finite laws. |
| §2.6 ([21](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=37)) | Extended-real carrier and claimed natural homomorphisms | **R/U** | [NumberPromotion](NumberPromotion.lean): `promotion_coherent` | Finite exact embeddings and tagged conversion are covered. A map out of F containing lambda is not specified into R plus signed infinities; preservation of rounded addition cannot be assumed. |
| §2.6.1 ([21–22](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=37)) | Positive infinitesimal and nonstandard-analysis discussion | **B/E/D** | [HyperrealInfinitesimal](HyperrealInfinitesimal.lean): `source_positive_infinitesimal` | The concrete inequality uses pinned mathlib. General transfer, smooth analysis and the signed-zero analogy are background discussion, not a verified IEEE conversion. |
| §2.6.2 ([22](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=38)) | Promotion versus demotion, explicit rounding stages | **E/R/U** | [DiscreteDemotion](DiscreteDemotion.lean): `down_greatest; up_least` | FiniteFormat.finite_directed and EndpointOptimality.certificate_exact_iff discharge actual finite-family extrema. General exceptional conversion and operation preservation still need semantics. |
| §2.6.3 ([22](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=38)) | Signed divergence with eventually-above/below quantifiers | **E** | [InfinityStreams](InfinityStreams.lean): `up_iff_extended_limit; down_iff_extended_limit; spikes_not_up` | This is exact sequence/limit correspondence, not a construction of a full quotient or transfer principle. |
| §2.7 ([23](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=39)) | An interval represents any enclosed fixed real | **E/R** | [ExactImageHull](ExactImageHull.lean): `sound` | HardwarePi supplies much stronger rational pi bounds. Native correctness and arbitrary exceptional numerical membership are separate. |
| §2.7.1 ([23](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=39)) | Ordered endpoints, width and real membership | **E/R** | [Intervals](Intervals.lean): `QInterval` | Ordered finite rational interval structure and real-set extended hulls are covered. Width of undefined/literal-infinite endpoint expressions is not silently EReal subtraction. |
| §2.7.2 ([24](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=40)) | Independent three-valued comparisons and Boolean projections | **E** | [StrictComparison](StrictComparison.lean): `compare_exact` | FiniteEquality.compareEQ_exact and DomainProjections.compareLE_exact/pessimistic_iff/optimistic_iff complete the finite named comparisons. Same-witness correlation does not imply both outcomes occur. |
| §2.7.3 ([24](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=40)) | Inclusion for arbitrary arity | **E/R** | [GeneralFamilyDemotion](GeneralFamilyDemotion.lean): `model_demotion; sound_demote` | Generic relational theorem retains actual witnesses. Concrete operator premises still require proof; this definition does not promise a universal operator synthesizer. |
| §2.7.4 ([25](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=41)) | Least image enclosure and outward endpoint demotion | **E** | [ExtendedImageHull](ExtendedImageHull.lean): `enclosure_iff; least; empty_hull` | Actual real images, including unbounded/empty, are handled; exact finite-family outward bounds are connected by EndpointOptimality. Printed text explicitly says extension is not a construction method. |
| §2.7.5 ([25](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=41)) | Subdistributivity, associative trails and singleton embedding | **E/C/R** | [RoundedIntervalControl](RoundedIntervalControl.lean): `staged` | IntervalAlgebra.subdistributive proves exact rational interval law. Least staged rounding refutes its unconditional floating-interval version. The singleton map alone is not an operation-preserving isomorphism of a nonclosed subtype; trail inclusion remains sound. |
| §2.8 ([26](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=42)) | Real-interval best enclosure | **E** | [ExtendedImageHull](ExtendedImageHull.lean): `sound; least; finite_agreement` | Bounds on real outputs are not genuine infinity members. No extrema-computation algorithm is claimed. |
| §2.9 ([26](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=42)) | Generalization by parameterized number descriptions | **E/R** | [GeneralFamilyDemotion](GeneralFamilyDemotion.lean): `exact_hull_sound` | Semantic framework and concrete families are proved; this is not one executable implementation of every possible family. |
| §2.9.1 ([26–27](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=42)) | Changing the endpoint number system | **E/R** | [NumberPromotion](NumberPromotion.lean): `down_greatest; up_least` | Integer and finite-rational target projectors are constructed. An arbitrary endpoint system needs representability/extremality premises; source supplies no universal projector. |
| §2.9.2 ([27](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=43)) | Boolean interval isomorphism and description inclusion | **E** | [BooleanComposition](BooleanComposition.lean): `conj_exact; disj_exact` | StrictComparison gives the three nonempty truth intervals. Independent images differ from correlated truth sets; no empty truth case/full lattice is asserted. |
| §2.9.3 ([27–30](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=43)) | Linear shared-parameter families and demotion | **E/C/R** | [LinearFamilyEquality](LinearFamilyEquality.lean): `canonical_or_full_fiber_of_range` | Finite affine correspondence/cancellation are proved. Pointwise forward-or-reverse assertion is refuted and repaired with a full-fiber alternative. AffineDemotionLimits.no_greatest_minorant closes the nonoptimality claim. Full exceptional coefficients remain unmodeled. |
| §2.9.4 ([30](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=46)) | Constant embedding and stated homomorphism | **E/R/U** | [LinearIntervals](LinearIntervals.lean): `linear_constant_add; linear_constant_sub`; [LinearMultiplication](LinearMultiplication.lean): `linear_constant_mul` | Concrete constant add/sub/mul and the success-conditioned evaluator correspondence are checked, including tests/ConstantEmbedding.lean. Extending this to arbitrary family/demotion choices needs compatibility, not mere inclusion. |
| §2.9.5 ([30](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=46)) | Quadratic bounds and invalid infinite-coefficient example | **E/R** | [QuadraticFamilies](QuadraticFamilies.lean): `one_parameter_representation; product_value` | ExceptionalFamilies checks the midpoint-to-lambda example. General literal exceptional coefficient arithmetic is not specified here; demotion implementation is explicitly deferred to later sections. |
| §2.9.6 ([30–31](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=46)) | Finite vectors of independent parameters, shared within each value | **E/R** | [MultiAffineFamilies](MultiAffineFamilies.lean): `hull_endpoints_attained` | Finite rational coefficient representation and exact extrema are covered; arbitrary real/exceptional coefficient system is a carrier generalization, not yet a full formal implementation. |
| §2.9.7 ([31](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=47)) | Coefficient function schema, noncollapse and inclusion | **E/R** | [GeneralFamilyDemotion](GeneralFamilyDemotion.lean): `model_demotion` | FunctionalBounds and arbitrary parameter/witness relations realize the semantic core. An arbitrary function family is a schema with operator/demotion obligations, not a supplied grammar or algorithm. |
| §2.9.8 ([32](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=48)) | Symbolic singleton bounds and finite expressions | **R/D** | [IntervalSetExtension](IntervalSetExtension.lean): `guarded_points_exact` | Exact graph/point semantics and finite arithmetic syntax exist. The displayed sin/root symbolic trace and a universal symbolic grammar are not directly formalized. The ellipsis is not an algorithmic specification. |
| §2.10 ([32–33](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=48)) | Ideal-to-stored and stored-to-evaluated outward bounds | **E/R/U** | [FiniteAffineDemotion](FiniteAffineDemotion.lean): `certified_enclosure; certified_evaluation` | Finite endpoint-basis certificate is proved, distinct from arbitrary coefficient demotion. The “order of machine precision” sentence lacks a norm/constant/conditioning hypothesis; it is not an established uniform error theorem. |
| §2.11 ([33–34](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=49)) | Value intervals with separate three-valued domain descriptions | **E/R** | [PartialEnclosures](PartialEnclosures.lean): `DomainBounds; PartialEnclosure` | Explicit definite/possible domains and same-witness partial semantics are covered. This is not a complete concrete syntax for every numeric descriptor. |
| §2.11.1 ([34](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=50)) | Value and domain inclusion | **E** | [GeneralFamilyDemotion](GeneralFamilyDemotion.lean): `sound_partial_iff; sound_demote` | Value obligations apply to actual outputs. No value is invented at an absent input or collapsed fiber. |
| §2.11.2 ([34–35](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=50)) | Value/domain extension and classification-preserving demotion | **E/R** | [DescriptorDemotion](DescriptorDemotion.lean): `integer_hull_refines` | Semantic criterion and real-to-integer-hull converter are proved. PieceDomainConversion provides an effective finite subclass; arbitrary classifier synthesis is not given by the source. |
| §2.11.3 ([35](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=51)) | Several domain classifiers with the same semantics | **E/R** | [DomainProjections](DomainProjections.lean): `numeric_refines; numeric_domain_refines` | Threshold/nonzero instances and tagged composition preserve classification. A common grammar for all classifiers is optional beyond the stated semantic interface. |
| §2.11.4 ([35–36](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=51)) | Conjunction of input domains plus partial-operation guard | **E/R** | [DomainConstraints](DomainConstraints.lean): `all_compatible; partial_guard_compatible` | FiniteProperties.composeN_defined is the exact strict domain factorization. RationalFamilyClosure proves generated finite arithmetic guards; arbitrary operations still need their guard. |
| §2.11.5 ([36](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=52)) | Simple flags and partial square-root examples | **E** | [SquareRootDomains](SquareRootDomains.lean): `sqrt_values_defined_iff` | Printed negative singleton with mixed domain is a loose sound enclosure, not a false statement. Precise classification is stronger than source permits here. |
| §2.12 ([36–37](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=52)) | Recursive weak/strong checking | **E/C/U** | [PropertyComposition fixtures](tests/PropertyComposition.lean): `printed_weak_direction_counterexample` | Strict definedness is compositional. Semantic-continuity reading of the printed weak arrow is refuted; structural certificates are a possible distinct interpretation, not an inferred correction. |
| §2.12.1 ([37](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=53)) | Definedness, continuity and coordinate-frozen local constancy | **E/R/C** | [FiniteProperties](FiniteProperties.lean): `composeN_defined; continuous_composeN` | TrackingCertificates.frozen_composeN is sufficient. Converse/necessity cannot be asserted; partial-domain hypotheses remain explicit. |
| §2.12.2 ([37–38](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=53)) | Value/property inclusion and description extension | **E/R/U** | [TrackingCertificates](TrackingCertificates.lean): `continuous_description` | Success-only certificate transport and exact domain descriptions are covered. Full literal weak-tracking recursion cannot be claimed until the source interpretation is resolved. |
| §2.12.3 ([38](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=54)) | Combining property systems and notation | **R/D** | [TrackingCertificates](TrackingCertificates.lean): `defined_description` | Separate domain/property obligations can be conjoined. Source notation and historical implementation claims do not specify a new algorithm requiring reconstruction. |
| §2.13 ([38–39](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=54)) | Interval sets as union denotation | **E** | [IntervalSetDenotation](IntervalSetDenotation.lean): `union` | Finite and arbitrary semantic piece sets retain one parameter; different pieces are not replaced by a single hull. |
| §2.13.1 ([39](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=55)) | Set extension, perfect guarded points and reciprocal rays | **E/R/U** | [IntervalSetExtension](IntervalSetExtension.lean): `extension_exact; lift_exact; guarded_points_exact` | SplitQuotient and finite output projection cover actual examples. Printed real V point collection is infinite; the following finite-description sentence refers to floating U, not the same object. General optimal finite-machine-family selection is not constructed. |
| §2.13.2 ([39](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=55)) | Definition of bumpy via strict improvement against all single models | **E/R** | [IntervalSetExtension](IntervalSetExtension.lean): `strict_against_every_interval` | The exact gap criterion and a finite witness are proved. No universal automatic bumpy classifier is stated or needed by this definition. |
| §2.14 ([40](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=56)) | Heterogeneous/equal interval coefficients and Hansen family | **E/R/U** | [HansenCoefficients](HansenCoefficients.lean): `signed_exact; exact_interval` | CoefficientWitnesses.coded_exact and MixedEndpoints compile concrete variants. HansenRealSets covers unbounded sets of finite choices. Literal infinite coefficients and cross-use choice convention are separate from pointwise exactness. |
| §2.15 ([40](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=56)) | Survey of real representations | **B/D** | [SECTION215_LEDGER.md](SECTION215_LEDGER.md): `page-and-claim ledger` | The source explicitly lets interval-only readers skip this survey. Imported constructions count as mathematical evidence, not newly verified implementations. |
| §2.15.1 ([40–41](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=56)) | Nonnegative cuts and pointwise rational arithmetic | **E/R** | [CutArithmetic](CutArithmetic.lean): `add_lub; mul_lub; operations_representation_independent` | Nonnegative inhabited proper cuts are handled, plus boundary conventions and signed-product failure. A signed-cut algorithm is not specified. |
| §2.15.2 ([41](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=57)) | Termwise rational-sequence arithmetic, representative independence | **E/R** | [SequenceRepresentations](SequenceRepresentations.lean): `add; mul; div` | Convergent sequences and guarded division are covered; no universal convergence rate is asserted in the source. |
| §2.15.3 ([41](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=57)) | Radix digits, floating place/sign, unique zero-tail convention | **E/U** | [FloatingDigits](FloatingDigits.lean): `coverage; normalized_representation_unique` | New scale normalization discharges all-real floating-place existence. DigitExtraction supplies canonical fractional uniqueness. Scale uniqueness needs the explicit leading-nonzero convention; carrying algorithm is not specified. Printed “second form” disagrees with its “tail of 0” wording. |
| §2.15.4 ([42](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=58)) | Finite/infinite simple fractions, recovery and rational termination | **E** | [InfiniteSimpleCF](InfiniteSimpleCF.lean): `admissible_reconstruction; representation_unique` | ContinuedFractionConversion covers finite normalization and actual mathlib Euclidean extraction. No arbitrary exact-real executable oracle follows. |
| §2.15.5 ([42–43](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=58)) | Converging interval arithmetic and accuracy search; first-digit obstruction | **E/R** | [ExpressionStreams](ExpressionStreams.lean): `eval_converges_encloses` | AccuracySearch gives executable supplied-stream search; FiniteQuery.no_total_decimal_reader/no_total_cf_reader proves the plain interval-oracle obstruction. The phrase “provided operators” refers onward to Chapter 3; proving every such operator is separate operator coverage, not a generic discontinuous composition theorem. |
| §2.15.6 ([43](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=59)) | Signed digit representation and cited online arithmetic | **E/R/D/U** | [DigitRepresentations](DigitRepresentations.lean): `signed_condition; partial_represents; addition` | Ordinary digits plus sign/scale embed in the signed alphabet. A fixed-delay carrying circuit is referenced but not specified; no implementation/rate result is proved here. |
| §2.15.7 ([43](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=59)) | Signed continued fractions, coverage and interval Euclidean extraction | **E/U** | [SignedExtraction](SignedExtraction.lean): `coverage; rational_extracts; finite_divisors_nonzero` | RedundantCF proves arbitrary admissible infinite convergence; generated all-real recovery/rational termination are closed. The interval extraction algorithm is unspecified; no uniqueness of redundant syntax is claimed. |
| §2.15.8 ([43](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=59)) | GIA can improve convergence and retains parameter information | **E/R/D** | [GeneralFamilyDemotion](GeneralFamilyDemotion.lean): `sound_demote` | Shared-parameter cancellation and symbolic singleton semantics support the qualitative examples. Source promises no universal speedup/rate or complete nonlinear solver. |

## What moved in this audit

The all-real floating-place statement in §2.15.3 now has a direct proof in
[FloatingDigits](FloatingDigits.lean). For every radix b ≥ 2, a nonzero real has
sign, integer exponent and canonical ordinary fractional digits with mantissa
in [1/b,1). Under this **explicit normalization convention**, sign, exponent and
digits are unique. Zero has a separately chosen representation. The source's
zero-tail convention by itself does not fix scale: 0.1 × 10 and 0.01 × 100
both represent 1. This is a noncomputable mathematical correspondence, not
extraction from a finite interval oracle or a hardware routine.

A second result closes a false proof target. In §2.7.5, exact interval
subdistributivity cannot be transferred unconditionally to staged floating
interval arithmetic. In the existing **literal** decimal format (10,3,−9,9),
use I=[2,2], J=[100,100], K=[1,1]. Least outward rounding gives J+K=[100,110],
then I·(J+K)=[200,220]; the other route gives I·J=[200,200], I·K=[2,2], then
[200,210]. The first contains 220 and the second does not.
`RoundedIntervalControl.staged` checks every least-rounded stage, not arbitrary
extra widening. The actual real answer 202 remains enclosed by both routes.
This does not refute the existing exact real/rational interval theorem.

## Remaining work, ranked by actual source obligation

1. **Unresolved semantics:** §§2.5–2.6 exceptional carrier/promotion and
   §2.12 weak-tracking interpretation. The five comparison predicates and
   specified operation rows are formalized; the source does not supply a
   complete exceptional operation table or a map for lambda into its displayed
   extended-real carrier. Weak semantic continuity contradicts checked masking
   examples. These need an explicit interpretation/errata decision, not an axiom.
2. **Precise correspondence still missing:** the literal symbolic sin/root
   trace of §2.9.8. Generic singleton/relational semantics are present, but that
   is not an audited concrete trace. Constant embedding for add/sub/mul and the
   existing linear evaluator is already proved; do not list that as missing.
   A universal claim for arbitrary inclusion-preserving demoters would need
   additional compatibility and is not implied by those concrete results. Full exceptional coefficient
   evaluations depend on item 1. The symbolic trace is a finite source-facing proof task.
3. **Restricted operator coverage:** §2.15.5 convergence is established for the
   finite strict arithmetic grammar, not every operator supplied later in the
   thesis. Additional operators belong to the operation/theory coverage plan;
   the source does not assert convergence for arbitrary discontinuous functions.

General quantifier elimination, automatic bumpy classification, arbitrary
optimal family demoters, online digit circuits, interval Euclidean extraction,
and uniform performance/ULP bounds are **not unproved universal Chapter 2
algorithms**: the chapter supplies definitions, references or qualitative claims,
not those specifications. They must not indefinitely enlarge this finish line.
The real V guarded-point collection on p.39 is infinite; the following finite
U description is a different floating family, not a direct self-contradiction.

**Defensible completion wording:** “Chapter 2 has a subsection-by-subsection
printed-source audit and a formalized core of real-valued inclusion, domain,
representation and conversion results. Imported foundations, restricted models,
checked counterexamples and underspecified claims are explicitly catalogued.”
Do not yet replace this with “every Chapter 2 claim is proved”: the concrete
correspondences above and the identified interpretation decisions remain.
