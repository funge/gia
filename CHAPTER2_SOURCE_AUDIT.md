# Chapter 2: claim audit and finish line

This is the consolidated source audit for the four integrated Chapter 2 units:
finite logic/domain, representations/bounds/exceptions, families/sets/demotion,
and properties/accuracy. **Chapter 2 is not complete.** It records current
source scope, not a claim that every sentence has been formalized. The
[completion plan](CHAPTER2_COMPLETION.md) and [checklist](CHAPTER2_CHECKLIST.md)
retain the acceptance criteria and detailed historical scope. Newer tagged
conversion is separate and is not included in this checkpoint.

Evidence: the original [thesis PDF](https://www.dgp.toronto.edu/~mooncake/thesis.pdf),
printed pp.13–43 (PDF pp.29–59), inspected page by page, including all eight
§2.15 subsections. The repository Markdown was an index, not the authority:
it omits §§2.15.4–8 and damages several formulas. Below, repeated inclusion,
infimum/supremum and demotion definitions have one obligation with cross-references,
not a separate task per occurrence. “Checked” means source correspondence at the
stated scope, not that all surrounding prose has a Lean theorem. Unmapped claims
remain open even when mathlib probably contains the necessary result.

Status: **E** exact stated semantic slice checked; **B** imported background;
**R** restricted counterpart, strengthening still needed; **O** unproved or
interpretation unresolved. Library pin: mathlib
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. No native correctness or additional
floating-point assumption follows from this audit.

## Claim-by-claim register

| Source (printed page) | Definitions and theorem-like claims; current evidence and remaining obligation |
| --- | --- |
| 2.1 (13–16) | **B:** carriers, arity, closure, ring identities, commutativity/associativity, order and distributivity use Lean `Int`, ring/order classes; `Int.cast_add` and cast homomorphisms supply promotion laws. **R:** source functions are partial, with λ and `dom`; `PartialRealArithmetic` gives guarded operations, not the whole source type theory. Subtraction/division notation must retain nonzero inverse guards. No multiplicative inverse for every integer. |
| 2.2 (16) | **B:** `Rat` normalized field/order and rational casts; **E:** `NumberPromotion.promotion_coherent`, `promoteInt_injective`, `promoteRat_injective`. **O mapping:** source irrationality of sqrt(2), no rational total square-root, and all source conversion homomorphism equations are not individually registered here. Available mathematics is not a completed correspondence. |
| 2.3 (17) | **B:** pinned `Mathlib.Data.Real.Basic` constructs `Real` from `CauSeq.Completion.Cauchy`; `Real.mk_add` respects quotient addition. Ordered-field laws are imported. **R:** source sqrt is undefined for negative inputs; `SquareRootDomains` supplies that guard, whereas bare `Real.sqrt` is totalized. Rational-Cauchy representative independence beyond the used library laws is background, not a new GIA theorem. |
| 2.4 (17–18) | **B:** `Mathlib.Data.Complex.Basic` defines the real pair and arithmetic. **O mapping:** total complex square-root, real embedding operation laws and impossibility of a compatible ordered field need explicit source-to-library witnesses. Doubling/quaternion discussion is survey, not an implemented interval domain. |
| 2.5 (18–21) | **R:** finite `Binary64.decode` and key/order proofs cover one radix/precision/exponent format, not generic F[b,A,m..M], alternate digit forms, rounding to nearest/up/down, decimal examples or ULP/algebra claims. **E mathematical finite-family rounding:** `DiscreteDemotion` constructs representable greatest lower/least upper endpoints, with exact decoded-binary64 value-family correspondence. Existing hardware directed contracts remain conditional, not verified implementations of these extrema. **E partial table:** `ExceptionalComparisons` all-five finite agreement and λ-false comparisons, same-sign infinity `<`/`=` false, with the remaining same-sign predicates derived by converse/disjunction (not complement). `NumberPromotion.rational_comparisons` preserves all five finite predicates; finite and positive-infinity addition, finite partial sqrt. Mixed exceptional comparison and arithmetic rows not specified by this layer remain **O**. The source lists five numerical comparisons, not a numerical `≠` table; λ sentinel tests are separate. |
| 2.6 (21–22) | **E:** `HyperrealInfinitesimal` realizes the positive-infinitesimal inequality using pinned mathlib. **R:** `NumberPromotion` exact embeddings and integer endpoint floor/ceil demotion; `ExtendedImageHull` uses infinities as *bounds on real outputs*. **O:** source F→R* “homomorphism” cannot automatically mean preservation of rounded operations; λ is not in the displayed R* carrier. **E:** `InfinityStreams` proves the printed integer-index rational tail criteria equivalent to rational signed divergence and EReal top/bottom limits, with unique mathematical tags and lambda unmapped. No quotient/transfer or exceptional operation theorem follows; operation conventions and the general source promotion remain open. Broad transfer prose and signed-zero/infinitesimal analogy are not established by the leaf theorem. |
| 2.7.1–2 (23–24) | **E finite:** ordered `QInterval`, real membership, zero-width singleton; `StrictComparison`, `FiniteEquality`, `DomainProjections` give exact independent Boolean outcomes and projections. **O:** exceptional endpoint width/membership/order. Correlated inputs do not inherit independent truth attainment. |
| 2.7.3 (24), repeated 2.9.7, 2.10, 2.11 | **E real-output semantic core:** `GeneralFamilyDemotion.sound_demote`, `model_demotion` preserve each actual shared witness, with domain-classification weakening separately required. Evaluator induction supplies concrete composition. **R:** arbitrary representation-specific operations/tuple decoders are not constructed by this theorem; its enclosure premises must actually be proved for each operator. |
| 2.7.4–2.8 (24–26) | **E real outputs:** `ExactImageHull` bounded nonempty hull, leastness/refinement and exact independent addition; `ExtendedImageHull` arbitrary real-output sets including empty/unbounded; `NumberPromotion` least integer-endpoint enclosure. **E finite-family mathematical demotion:** `DiscreteDemotion` proves least outward bounds, empty/unbounded controls and nested-family conversion. **O:** general source-format construction/native refinement, exceptional numerical outputs and full operation algebra. **E finite exact:** `IntervalAlgebra.subdistributive` and `addition_trail` cover the displayed §2.7.5 p.25 laws for unchanged rational operations; a strict-containment control rules out equality. Arbitrary backend widening is not covered. Degenerate scalar embedding is a representation correspondence, not automatically an operation-preserving interval isomorphism. The remaining machine-level algebra cannot be inferred from inclusion alone. |
| 2.9.1 (26) | **E:** real-output hull with exact extended-integer outward projection. **E finite rational target families:** `DiscreteDemotion` constructs an extremal projector and specializes it to decoded binary64 values. **R:** arbitrary numeric-type I(X) still needs a proven target projector, not merely the assumed `Demotes` condition. |
| 2.9.2 (27) | **E:** `BooleanComposition`, finite three nonempty truth intervals, independent exact ∧/∨ images, correlation-safe subset and counterexamples; description inclusion distinct from truth order. Negation is a derived extension. No empty truth interval/full lattice claimed. |
| 2.9.3 (28–30) | **E finite rational instance:** `QAffine`, `LinearInterval`, coefficient correspondence, pointwise containment and shared parameter cancellation. **E general real obstruction added here:** `AffineDemotionLimits.no_greatest_minorant`; there need not be a greatest affine lower demotion. **O:** full extended-coefficient family/undefined bound expressions; the source claim about every interval representative containing a forward/reverse representative is refuted under pointwise containment by `LinearFamilyEquality.shrinking_range` and its two noncontainment theorems; total-range containment is a distinct reading. **E corrected finite alternative:** `canonical_or_full_fiber_of_range` proves forward/reverse pointwise containment OR a full endpoint fiber, with exact projected range required. See [precise scope](LINEAR_FAMILY_EQUALITY.md). “No best in general” does not say every affine input lacks a best bound. |
| 2.9.4–6 (30–31) | **E restricted:** constant embedding/hull demotion; finite polynomial/quadratic instances. **E finite rational multi-parameter:** [MultiAffineFamilies](MULTI_AFFINE_FAMILIES.md) supplies the source cube representation, exact extremum/noncollapse/inclusion criteria, same-vector affine operations, one-parameter correspondence and least constant hull/demotion. **E finite quadratic:** [QuadraticFamilies](QUADRATIC_FAMILIES.md) gives exact one-parameter coefficient semantics and affine embedding, exact shared-vector affine products/add/sub/scale, semantic noncollapse and sound demotion; cross-term n>1 forms are a derived extension. **E finite chain:** [FiniteFamilyChain](FINITE_FAMILY_CHAIN.md) constructs a general one-parameter quadratic-to-affine demoter from the existing chord bound, proves affine promotion/demotion round-trip and injectivity, composes constant projection, and retains exact same-witness partial domains. Bubble and square controls distinguish useful tightening from nonoptimality. **E specified exceptional example:** [ExceptionalFamilies](EXCEPTIONAL_FAMILIES.md) formalizes the explicit ∞−∞α midpoint-to-λ row, distinguishes literal evaluation from real-family images and EReal bound arithmetic, and proves exact independent/shared images. **O:** full real/extended coefficient carriers, remaining exceptional evaluation rows and general nonlinear operator demotion/optimization. |
| 2.9.7–8 (31–32) | **E semantic core:** arbitrary parameter in `FunctionalBounds`, `GeneralFamilyDemotion`; actual outputs and partiality explicit. **R:** concrete coefficient-family and symbolic syntax realization. The source singleton symbolic expression and finite-support representation are not all formalized; semantic sets are not a supplied symbolic converter. |
| 2.10 (32–33) | **E restricted:** finite raw-word endpoint candidate certification, noncollapse, conditional outward interpolation at the same parameter. **O:** general machine-coefficient family demotion and evaluation correspondence; “of order machine precision” has no quantified bound here. No optimal affine converter is required (2.9.3), and no ULP claim is proved. |
| 2.11.1–3 (33–35) | **E core:** `DomainBounds`, exact possible/definite envelopes, numeric threshold/nonzero descriptions and classification-preserving re-encoding. **R:** full numeric f(d) language and automatic demotion; source classification equivalence and optimistic projection cannot be replaced by arbitrary interval widening without premises. Undefined fibers impose no numeric value obligation. |
| 2.11.4–5 (35–36) | **E same-parameter:** `DomainConstraints` conjunction and partial-operation domain guards, `GeneralFamilyDemotion` classification weakening. **R:** arbitrary representation generation and full source notation. Total operators retain input obligations; partial operators add their own. Printed negative singleton sqrt with uncertain domain is loose but sound, not a contradiction: no value needs enclosure. |
| 2.12 (36–38) | **E actual partial-function core:** `PartialProperties`, `FiniteProperties` strict finite-arity definedness iff all inputs and outer operation defined; sufficient continuity/local-constancy transport. **O interpretation:** printed weak-tracking arrow composite→recursive fails for semantic continuity (masking by constant/square outer function; `PropertyComposition`). Sufficient reverse transport is not a repair or evidence of authorial intent. **E corrected sufficient counterpart:** `TrackingCertificates` reuses finite-arity continuity and transports certificate descriptions by keeping definite success while making failure inconclusive; the square/jump control refutes copying a false possible flag. Its separate strict domain factorization/description closure is an exact iff. `frozen_composeN` now supplies a source-shaped coordinate-freezing sufficient local-constancy rule with explicit tuple convergence and actual point/nearby values; projection and identity controls distinguish it from all-child constancy. Full source property-description recursion and the printed weak interpretation remain open. |
| 2.13 (38–39) | **E real sets:** `IntervalSetDenotation` existential pieces, union/intersection, point representation, least real/integer hull; split quotient witnesses. **E general real-output extension:** [IntervalSetExtension](INTERVAL_SET_EXTENSION.md) proves arbitrary-piece finite-arity lifting at one shared parameter, exactness vs enclosure, and the squared-distance guard/perfect partial-point representation on a common domain. Its gap criterion proves strict improvement against every enclosing closed interval, instantiated by a finite two-piece jump model. **E finite rational point-code iff:** [FinitePointDescriptions](FINITE_DESCRIPTIONS_AND_CUTS.md) characterizes exact finite-table representability by finite graph plus rational decoder coverage; arbitrary predicates are not counted as finite codes. **R:** general finite piece/guard language and constructive demotion, exceptional outputs; no universal classification for every parameter-dependent base family. |
| 2.14 (39–40) | **E finite independent coefficients:** `IntervalCoefficientVariants.exact_form`, at one fixed nonnegative parameter, and scalar equal bounds. **O:** general heterogeneous coefficient types, persistent coefficient witnesses across parameters, Hansen multi-parameter variant, open endpoint types. Equal interval descriptions need not represent a singleton; coefficient correlation is not Cartesian choice. |
| 2.15.1 (40–41) | **E:** [DedekindBoundary](FINITE_DESCRIPTIONS_AND_CUTS.md) proves nonnegative real lub for every proper nonempty downward-closed nonnegative rational cut; principal strict/closed positive cuts decode equally but differ at rational boundaries. Empty strict zero cuts expose the ambient-order/totalized-sSup distinction. **E:** [CutArithmetic](CUT_ARITHMETIC.md) proves the displayed pointwise rational addition and nonnegative multiplication decode correctly, preserve proper nonempty downward cuts, and are independent of representative choice after decoding; derived decoded order is upper-bound-test inclusion. The printed signed-product warning has a witnessed counterexample. **O:** full signed construction and other operation-specific inheritance; boundary conventions must not be silently identified as equal descriptions. |
| 2.15.2 (41) | **B:** mathlib rational Cauchy quotient. **E:** [sequence package](SEQUENCE_AND_DIGIT_REPRESENTATIONS.md) connects every converging rational stream to `Real.mk`, proves termwise +/−/× and representative independence under explicit continuous-operation/cast premises, and eventual quotient correctness for a nonzero limit denominator. Zero-limit and delayed-prefix controls prevent an unconditional partial-operation or stopping-rate claim. |
| 2.15.3 (41) | **E normalized integer digits:** [digit package](SEQUENCE_AND_DIGIT_REPRESENTATIONS.md) proves summability, [0,1] range, rational partial-sum representation and a derived truncation bound; exact termwise addition before carrying and the general terminating/repeating equality. **O:** canonical extraction/existence/uniqueness, carrying and floating-place normalization. |
| 2.15.4 (42) | **E constructed expansion:** [ContinuedFractionConversion](CONTINUED_FRACTION_CONVERSION.md) reuses pinned mathlib’s floor/reciprocal construction and rational-iff-termination theorem, proves an explicit stopping bound and exact rational recovery, and preserves the entire expansion under real promotion. **E constructed canonical properties:** final non-initial coefficient ≥2 (also in public stored pairs), no terminal 1, and injectivity for constructed rational expansions; local terminal-1 contraction uses actual finite `GenContFract` representations. **E finite integral simple presentations:** arbitrary-prefix terminal-1 contraction, positivity of all valid tails, reconstruction of each normalized finite presentation by the actual constructor, and head/list uniqueness from decoded equality. Empty tails and noncanonical terminal-1 controls are included. **E infinite canonical:** pinned mathlib convergence/epsilon recovery audited directly, irrational nontermination and nonexact finite truncations, all-real constructor injectivity, and exact translation to existing rational-stream semantics. **O:** reconstruction/uniqueness for arbitrary admissible infinite streams and broader nonintegral/generalized numerators; no malformed-input or computable real-oracle claim. |
| 2.15.5 (42–43) | **E real-endpoint slice added here:** `ReciprocalStreams.converges` proves eventual guard success and reciprocal endpoint convergence for ordered bounds with the same nonzero limit; `eventual_enclosure` keeps the same-index value witness. **E restricted composition:** `ExpressionStreams` reuses rational `eval` for strict finite +/−/×/÷ expressions, with eventual success/enclosure/convergence and a terminating rational width search for supplied executable streams. The wrapper has generated-C object compilation and Lean execution evidence; a nested-division example rejects two stages then succeeds. Input computability is an execution obligation, not a consequence of convergence; endpoint containment is required for a limit-value certificate. **O:** construction of general real representations, remaining source operators and stated extraction obstructions. No a priori modulus or hardware refinement follows. |
| 2.15.6 (43) | **E normalized integer digits:** [digit package](SEQUENCE_AND_DIGIT_REPRESENTATIONS.md) proves exact translation of −b<d<b, summability, [−1,1] range, rational partial-sum convergence and truncation bound, addition/negation and nonunique zero control. **O:** all-real digit construction/place normalization and online algorithm/delay claims. |
| 2.15.7–8 (43) | **O:** redundant continued-fraction conditions and algorithm; generalized intervals' convergence advantage and symbolic exactness. Some performance narrative references later chapters, but remaining mathematical claims need correspondence. No speed claim follows from these proofs. |

## Smallest finish-line list (deduplicated)

1. **Representation/exception bridge:** finish the supported source carriers,
   promotion, numerical comparisons and arithmetic cases; distinguish bound order,
   λ sentinel tests and numerical comparisons. Resolve only genuine source forks;
   do not complete an unspecified table by guessing IEEE behavior.
2. **Family realization and demotion:** instantiate the common semantic theorem
   with source quadratic/multi-parameter/functional/symbolic families and their
   actual converters. Prove noncollapse and partial-domain obligations. Do not
   demand a nonexistent universal optimal affine bound. Tie machine-family
   statements to approved contracts and explicitly leave any precision claim open.
3. **Operation/domain/property closure:** source interval algebra and n-ary
   correspondence, numeric domain descriptors, and a documented resolution of
   weak tracking. Conditional sufficient continuity is not the printed equivalence.
4. **Set/variant completion:** general real-output lifting and the perfect-point
   equality guard are now checked, as is a quantified constant-interval gap
   criterion. Remaining finite encoding, open/exceptional and
   multi-parameter rows; quantified bumpy claims, or a precise accepted limitation.
5. **Foundation/representation correspondence:** finish the explicit imported
   mathematics mapping and §2.15's proof-bearing claims, especially convergence.
   The survey is not a mandate to implement new numeric runtimes.

The most consequential positive gap identified was guarded reciprocal convergence
(§2.15.5), now closed at the exact real-endpoint level by
[ReciprocalStreams.lean](ReciprocalStreams.lean). For `l,u : ℕ → ℝ` converging
to the same `r ≠ 0`, with `∀ n, l n ≤ u n`, `converges` proves eventual success
of the guarded reciprocal interval `(1/u n,1/l n)` and convergence of both output
endpoints to `1/r`. `evaluate_sound` and `eventual_enclosure` prove containment
for **every** same-index input value and exclude zero. This is a noncomputable
mathematical operation, not another runtime evaluator. It reuses mathlib inverse
continuity and reciprocal order, without assuming a convergence conclusion.
Nestedness and enclosure of the limit are not needed for this stronger endpoint
statement; they can be supplied by a source stream. No success is asserted before
the eventual guard. The whole interval, not merely the limit, must avoid zero.

[Controls](tests/ReciprocalStreams.lean) cover positive/negative intervals,
reversal, touching zero, and a constant zero stream falsifying any removal of
`r ≠ 0`. The nonconstant fixture `[1−1/(n+1),1+1/(n+1)]` initially fails but
eventually succeeds with both reciprocal bounds converging to 1.

The finite-expression arithmetic step is now proved in
[ExpressionStreams](EXPRESSION_STREAMS.md), reusing the existing `Expr`, strict
`Value`, and `eval exactBackend`: rational constants, x/y, +, −, × and guarded ÷.
The theorem gives eventual success, same-index enclosure and endpoint convergence.
It also proves a rational width test and a terminating `Nat.find` search under
those premises; input containment is separately required for a limit-value error
certificate. This does not construct executable representations of arbitrary
reals, prove all source operators convergent, or transfer to fixed-precision FP.
The next generalization is the source's remaining operator/representation
correspondence with explicit continuity/domain conditions, not an unconditional
claim for arbitrary partial or discontinuous operations.

## New source theorem: affine demotion need not have a best choice

[AffineDemotionLimits.lean](AffineDemotionLimits.lean) formalizes the printed p.30
claim without changing the family APIs. `Minorant m c` means
`∀ t ∈ [0,1], m*t+c ≤ t²`. Both `0` and `2*t−1` satisfy it. A putative greatest
minorant would dominate both, hence have values 0 at 0 and 1 at 1. Affinity forces
value 1/2 at 1/2, contradicting square's value 1/4. This proves nonexistence over
**all real coefficients**, not just failure of a supplied rational candidate.
Negation gives no least affine majorant of negative square. It is a source-defined
negative result, separate from the positive convergence theorem above.

[The fixtures](tests/AffineDemotionLimits.lean) check crossing candidates, failed
single-affine replacement, sound retained conjunction and an affine target that
*does* have a greatest bound. No claim of unattainable function values, native
execution, exact rounding or a newly trusted axiom is involved. The earlier
positive-domain obstruction in `AffineConjunction` is preserved; it concerns a
different endpoint-preservation requirement, not universal pointwise greatestness.


## Current exceptional-row checkpoint

The five-predicate extension closes the explicitly named lambda rows and derived
converse/disjunction rows of the supported table; see the evidence partition in
[Exceptional comparisons](EXCEPTIONAL_COMPARISONS.md). It does not settle mixed
exceptional directions, exceptional arithmetic or lambda promotion. `none` stays
unmodeled, not source false or undefined. The remaining blockers above are
unchanged in kind; §2.6.3's rational-sequence characterization is now proved in
[InfinityStreams](INFINITY_STREAMS.md), without importing numerical exceptional
comparisons. The remaining promotion obligation is the general source carrier
and operation correspondence, especially the missing lambda map and distinction
between exact embedding and rounded arithmetic.


## §2.12 interpretation checkpoint

Printed pp.36–37 / PDF pp.52–53 were rechecked for both arrows and the semantic
versus checkable definitions. The original semantic weak direction remains
refuted; neighboring domain examples do not identify the author's intended fix.
[Tracking certificates](TRACKING_CERTIFICATES.md) records the literal and
conservative structural readings separately, proves a sufficient description
transport without a necessity claim, and advances independent exact strict
domain-description closure. The nonconstant square/jump control strengthens
the preserved counterexample. This does not close full source weak tracking.

## Descriptor conversion closure (§2.11.2–3, printed p.35 / PDF p.51)

[DescriptorDemotion](DESCRIPTOR_DEMOTION.md) instantiates classification-preserving
conversion beyond finite affine families: arbitrary real descriptor sets are
converted by the existing outward integer-endpoint hull, with classification
refinement for any predicate. Empty and unbounded fibers are covered. The exact
extra condition for plain subset widening is proved, not assumed silently.
Loss of lambda during successful-bound projection has a checked counterexample;
retaining the original domain restores same-tag compatibility. This checks a
specific conversion and general semantic criterion, not every source carrier,
exceptional arithmetic table or arbitrary classifier implementation.
