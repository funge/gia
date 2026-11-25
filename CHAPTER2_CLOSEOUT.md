# Chapter 2 closeout matrix

**Chapter 2 is not complete.** This matrix consolidates the current residuals after the finite value/domain converter and guarded composition bridge; older milestone notes remain historical evidence. “Covered” always means the stated scope, not every surrounding claim. See the [source audit](CHAPTER2_SOURCE_AUDIT.md) for printed pages and detailed theorem mappings, and the [concordance](THESIS_CONCORDANCE.md) for the broader project.

| Source / obligation | Status | Current evidence or precise remaining work |
| --- | --- | --- |
| §§2.1–2.4 scalar foundations | Covered explicit scalar correspondence | [Numeric foundations](NUMERIC_FOUNDATIONS.md) registers actual embedding laws, guarded division, rational-root obstructions, real-root domain, total complex-root existence, rational-sequence existence and ordered-ring incompatibility. Ordinary scalar constructions use pinned mathlib; surrounding survey narrative is not all formalized. |
| §2.5 finite format and directed bounds | Covered mathematical slices | Arbitrary-radix literal family, separately repaired normalization, repaired binary64 finite-value iff, and optimal-certificate correspondence are proved. [Directed operation algebra](DIRECTED_OPERATION_ALGEBRA.md) now proves exact finite success/optimality, commutativity, represented identities/cancellation and small nonassociativity controls. [Source-rounded algebra](SOURCE_ROUNDED_ALGEBRA.md) checks both decimal conventions, exposes incompatible printed rows, proves derived multiplication nonassociativity and refutes every five-site rounding assignment in the stated distributive formula. [Nearest minimizers](NEAREST_MINIMIZERS.md) now closes finite real-input existence, strict uniqueness and adjacent-midpoint ties without selection; decimal nonzero inverse failures and a small-format scope counterexample are checked. Tie selection/exceptional overflow require specification; ULP claims remain separate. No hardware correctness follows. |
| §2.5 coefficient versus digit displays | Inconsistent as unconditional value-set equality | The uniform maximum-exponent counterexample is checked. The repaired convention remains separately named; intended correction is not established by proof. |
| §§2.5–2.6 exceptional comparisons/arithmetic | Covered explicit subset; semantics not specified for remaining rows | Five finite predicates, specified λ/infinity rows and selected operations are modeled. The source-supported reversed finite/positive-infinity addition row is now a conservative extension; mixed infinities, λ operands and infinite-input roots remain unmodeled. Do not invent missing numerical comparison rules. Any additional row requires source evidence first. |
| §2.6 promotion and limits | Covered slices; semantic interpretation open | Finite embeddings, signed divergence and positive infinitesimal example are proved. A source “homomorphism” cannot silently mean preservation of rounded arithmetic. Full exceptional carrier/operation correspondence requires specified operations; λ is not in the displayed extended-real carrier. |
| §§2.7–2.8 intervals and image hulls | Covered real-output core; proof gaps beyond it | Exact independent finite comparisons, real hull leastness including empty/unbounded sets, finite algebra and discrete demotion are covered. Exceptional numerical output membership/order and remaining source operation algebra need separate semantics/proofs. |
| §§2.9–2.10 general family inclusion | Covered generic theorem and finite instances | Same-witness inclusion/demotion, finite multi-affine/quadratic/constant conversions, finite machine-candidate certificates and conditional outward evaluation are proved. A generic soundness interface does not construct all source family operations or converters. Full supported functional/symbolic families and exceptional coefficient evaluations remain gaps. |
| §2.9.3 forward/reverse representative claim | Inconsistent under pointwise-containment reading | The counterexample and corrected orientation-or-full-endpoint-fiber theorem are checked. Projected-range containment is a different reading; authorial intent remains open. No universal best affine demoter is asserted. |
| §2.9.2 Boolean interval logic | Covered finite exact semantics | Independent Boolean images, correlation-safe inclusion and distinction from conservative unknown are proved. No empty truth interval or unspecified exceptional Boolean algebra is claimed. |
| §2.11 value plus domain conversion | Covered first constructive subclass; major proof gap remains | [Finite guarded mixed bands](PIECE_DOMAIN_CONVERSION.md) now construct numeric enclosure and explicit feasibility code, preserving per-choice definite/possible classification. [Guarded composition](GUARDED_PIECE_COMPOSITION.md) now integrates generated guards with the existing expression evaluator on checked success, preserving same-choice classifications and value enclosure. [Affine reciprocal splitting](AFFINE_POLE_SPLIT.md) now generates exact negative/zero/positive domain pieces even when the hull guard fails. [Unbounded piece composition](UNBOUNDED_PIECE_COMPOSITION.md) retains these guards through exact affine translation with sound values and exact domain. [Rational-expression closure](RATIONAL_FAMILY_CLOSURE.md) now constructs exact polynomial graphs and inherited guards for every existing arithmetic expression, preserving same-choice classifications without whole-hull success. [Fractional projection](FRACTIONAL_PROJECTION.md) now eliminates the input witness for certified regular fractional-linear values, including canceled expressions, and proves an effective rational image-membership query. [Finite monotone unions](MONOTONE_UNIONS.md) now give exact union projection and effective square output-piece enumeration, preserving flags and guards. General branch discovery, nonlinear output conversion/demotion and operators beyond this grammar remain missing; failed choices cannot be dropped. |
| §2.11 partial-operation image conversion | Covered common criterion and controls | [Injective partial-image transfer](PARTIAL_IMAGE_TRANSFER.md), root and reciprocal instances, finite-gap certificates. Exact image equality alone does not preserve universal definedness; arbitrary gap discovery and arbitrary operator closure are not proved. |
| §2.12 strict domains and sufficient properties | Covered common mathematical core | Strict finite-arity domain factorization, sufficient continuity/local constancy and certificate transport are proved. Full recursive property-description generation remains a proof task once its intended semantics is fixed. |
| §2.12 printed weak-tracking direction | Inconsistent under semantic-continuity reading | Constant/square masking counterexamples refute the proposed converse. A structural certificate interpretation is possible but is not automatically the source's intended repair; failure must remain inconclusive. |
| §§2.13–2.14 finite sets/variants | Covered explicit finite models; broader representation gaps | Exact guarded-piece compilation, mixed open boundaries, persistent coefficient witnesses, finite Hansen pointwise ranges and unbounded sets of finite coefficients are covered. Arbitrary bumpy/function representation and literal exceptional coefficient arithmetic are not obtained. General constructive demotion beyond supported pieces remains missing. |
| §2.15.1 cuts | Covered nonnegative construction/operations and signed-product warning | The source does not supply a signed-cut operation construction; that optional extension is not a missing asserted theorem. Strict/closed descriptions must not be identified structurally merely because they decode equally. See the [page-and-claim ledger](SECTION215_LEDGER.md). |
| §2.15.2 Cauchy streams | Covered stated arithmetic slice | Rational-stream representation, arithmetic and representative independence with guarded division are proved. No generic computable real oracle is implied. |
| §§2.15.3, 2.15.6 digit streams | Covered ordinary canonical construction and signed sums; algorithm gaps | [Digit extraction](DIGIT_EXTRACTION.md) now proves ordinary canonical reconstruction/uniqueness and all-real integer-part representations. Floating-place normalization, effective carrying and source online/delay claims remain distinct from this noncomputable correspondence. |
| §2.15.4 continued fractions | Covered finite and arbitrary infinite simple correspondence | [Infinite simple fractions](INFINITE_SIMPLE_CF.md) now prove arbitrary admissible stream convergence, canonical recovery, irrationality and coefficient uniqueness, complementing the finite reconstruction and rational-termination proofs. Generalized numerators are not part of this displayed source claim. |
| §2.15.5 interval streams / accuracy | Covered finite strict arithmetic grammar; proof gaps | Same-stream convergence and executable certified search are proved under computable-stream/containment premises. [Finite-query obstruction](FINITE_QUERY.md) now closes the canonical decimal/CF first-term limitation for plain nested rational interval oracles, with constructive indistinguishable names and actual adaptive traces. Remaining source operators and richer computation models require separate correspondence; no arbitrary-precision hardware implementation follows. |
| §2.15.7 redundant fractions | Covered mathematical coverage and rational constructor; interval algorithm unspecified | [Signed extraction](SIGNED_EXTRACTION.md) constructs valid finite/infinite expansions of every real with exact recovery and proves rational termination plus an executable bounded rational constructor. A labeled lower-tie convention satisfies every generated suffix restriction, including the finite last term. Earlier arbitrary infinite convergence and finite nonuniqueness remain. The source mentions but does not specify interval Euclidean extraction; arbitrary redundant uniqueness and invalid finite syntax are not silently repaired. |
| §2.15.8 GIA representations | Expository correspondence; later-chapter quantitative claims | The source says improved convergence can occur and gives symbolic intervals as an immediate but unproductive example; it states no uniform improvement theorem or rate. Same-witness functional semantics are established; specified operation advantages and later graphing claims remain distinct. |

## Recommended finite closeout program

The new [unbounded-piece composition](UNBOUNDED_PIECE_COMPOSITION.md) closes an
actual representation/composition gap: the existing finite descriptions now
carry reciprocal rays through affine addition while preserving guards and exact
domain nonemptiness. It does not justify calling every nonlinear function
finitely representable. Further isolated variants should not be the default
next task. The smallest useful remaining program is **three substantial proof
packages plus one explicit source-resolution review**, not a promise of three
small PRs:

1. **Numeric foundation correspondence (§§2.1–2.8).** Register the missing exact
   scalar/mathlib mappings, finish source-required rounding and operation laws
   for the already specified mathematical carriers, and connect their domains
   to the existing exceptional tags. Separate mathematical rounding from native
   execution. Exit evidence is a declaration-level mapping for every explicit
   source rule, with no guessed exceptional rows. Finite nearest existence and
   tie characterization are now proved without selection; any selected tie or
   exceptional overflow result still needs an explicit convention.
2. **Family/operator closure (§§2.9–2.14).** Audit the printed operator and
   conversion claims against the generic same-witness family theorems, then
   discharge missing concrete premises for the source-supported families in one
   shared value/domain/property composition chain. Use the existing partial
   relations, guards, sets and tagged conversions. The rational-expression graph compiler now closes the arithmetic/domain
   construction for the existing grammar; representation-specific output
   elimination/demotion and property generation remain separate obligations.
   Certified fractional-linear projection now has an exact descriptor and
   complete rational query; exact monotone union projection and square-piece generation are now proved. General root/sign decomposition remains open. Exit evidence must distinguish
   exact representation, enclosure and classification for every claimed
   operator; unsupported arbitrary nonlinear/bumpy descriptions stay explicit,
   rather than being hidden behind an assumed inclusion hypothesis.
3. **Representation survey closure (§2.15) and final cross-reference gate.**
   Map all eight subsections to actual pinned library/project results. Prove the
   remaining proof-bearing extraction/conversion or convergence statements only
   where the source asserts them; do not implement a new real-number runtime or
   extend continued-fraction examples merely to add variants. Preserve the
   distinction between canonical expansions and arbitrary streams. Finish with
   a source-claim/theorem/premise inventory covering the entire chapter.

**Source-resolution review is a separate prerequisite for an honest “complete”
claim.** The literal coefficient/digit equality, pointwise orientation reading
and weak semantic-continuity converse have checked counterexamples. The author’s
intended correction is not established by our repaired theorems. The project
must explicitly accept a documented errata/interpretation treatment, or retain
those rows as unresolved. Unspecified exceptional arithmetic rows cannot be
proved or filled with IEEE rules. No new FP assumption is proposed here.

These are recommendations for organizing the existing finish-line obligations,
not a narrowed definition of done or evidence that the remaining proofs are
trivial. In particular, the source’s general representation statements must be
read as stated before deciding whether a generic set theorem already closes them
or a constructive claim remains. Chapter 2 remains incomplete.

## §2.15 source-led priority after finite branch projection

The [page-and-claim ledger](SECTION215_LEDGER.md) now covers all eight subsections.
The ordinary canonical digit converse is proved, not merely another example.
The arbitrary admissible infinite simple-stream converse is now proved.
The printed-admissible redundant infinite class (§2.15.7) now has a proved
convergent, defined suffix interpretation. The signed coverage and exact-rational extraction obligation is now closed by a
source-compatible nearest-integer construction with an explicitly labeled tie
choice. Its generated finite suffixes are all defined. The remaining interval
Euclidean algorithm needs an operational specification; the arbitrary finite
terminal-zero syntax limitation remains separate. The first-digit finite-information obstruction now has an explicit deterministic
indexed-oracle model and constructive rational counterexamples. Enriched names
and redundant output are outside that theorem. No arbitrary nonlinear closure implementation is
added to the chapter finish line merely because finite projection tools exist.
