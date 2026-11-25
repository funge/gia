# Chapter 2 closeout matrix

**Chapter 2 is not complete.** This matrix consolidates the current residuals after the finite value/domain converter and guarded composition bridge; older milestone notes remain historical evidence. “Covered” always means the stated scope, not every surrounding claim. See the [source audit](CHAPTER2_SOURCE_AUDIT.md) for printed pages and detailed theorem mappings, and the [concordance](THESIS_CONCORDANCE.md) for the broader project.

| Source / obligation | Status | Current evidence or precise remaining work |
| --- | --- | --- |
| §§2.1–2.4 scalar foundations | Covered explicit scalar correspondence | [Numeric foundations](NUMERIC_FOUNDATIONS.md) registers actual embedding laws, guarded division, rational-root obstructions, real-root domain, total complex-root existence, rational-sequence existence and ordered-ring incompatibility. Ordinary scalar constructions use pinned mathlib; surrounding survey narrative is not all formalized. |
| §2.5 finite format and directed bounds | Covered mathematical slices | Arbitrary-radix literal family, separately repaired normalization, repaired binary64 finite-value iff, and optimal-certificate correspondence are proved. [Directed operation algebra](DIRECTED_OPERATION_ALGEBRA.md) now proves exact finite success/optimality, commutativity, represented identities/cancellation and small nonassociativity controls. [Source-rounded algebra](SOURCE_ROUNDED_ALGEBRA.md) checks both decimal conventions, exposes incompatible printed rows, proves derived multiplication nonassociativity and refutes every five-site rounding assignment in the stated distributive formula. Global nearest selection/ties, ULP claims and broader inverse-law scope remain distinct. No hardware correctness follows. |
| §2.5 coefficient versus digit displays | Inconsistent as unconditional value-set equality | The uniform maximum-exponent counterexample is checked. The repaired convention remains separately named; intended correction is not established by proof. |
| §§2.5–2.6 exceptional comparisons/arithmetic | Covered explicit subset; semantics not specified for remaining rows | Five finite predicates, specified λ/infinity rows and selected operations are modeled. The source-supported reversed finite/positive-infinity addition row is now a conservative extension; mixed infinities, λ operands and infinite-input roots remain unmodeled. Do not invent missing numerical comparison rules. Any additional row requires source evidence first. |
| §2.6 promotion and limits | Covered slices; semantic interpretation open | Finite embeddings, signed divergence and positive infinitesimal example are proved. A source “homomorphism” cannot silently mean preservation of rounded arithmetic. Full exceptional carrier/operation correspondence requires specified operations; λ is not in the displayed extended-real carrier. |
| §§2.7–2.8 intervals and image hulls | Covered real-output core; proof gaps beyond it | Exact independent finite comparisons, real hull leastness including empty/unbounded sets, finite algebra and discrete demotion are covered. Exceptional numerical output membership/order and remaining source operation algebra need separate semantics/proofs. |
| §§2.9–2.10 general family inclusion | Covered generic theorem and finite instances | Same-witness inclusion/demotion, finite multi-affine/quadratic/constant conversions, finite machine-candidate certificates and conditional outward evaluation are proved. A generic soundness interface does not construct all source family operations or converters. Full supported functional/symbolic families and exceptional coefficient evaluations remain gaps. |
| §2.9.3 forward/reverse representative claim | Inconsistent under pointwise-containment reading | The counterexample and corrected orientation-or-full-endpoint-fiber theorem are checked. Projected-range containment is a different reading; authorial intent remains open. No universal best affine demoter is asserted. |
| §2.9.2 Boolean interval logic | Covered finite exact semantics | Independent Boolean images, correlation-safe inclusion and distinction from conservative unknown are proved. No empty truth interval or unspecified exceptional Boolean algebra is claimed. |
| §2.11 value plus domain conversion | Covered first constructive subclass; major proof gap remains | [Finite guarded mixed bands](PIECE_DOMAIN_CONVERSION.md) now construct numeric enclosure and explicit feasibility code, preserving per-choice definite/possible classification. [Guarded composition](GUARDED_PIECE_COMPOSITION.md) now integrates generated guards with the existing expression evaluator on checked success, preserving same-choice classifications and value enclosure. [Affine reciprocal splitting](AFFINE_POLE_SPLIT.md) now generates exact negative/zero/positive domain pieces even when the hull guard fails. [Unbounded piece composition](UNBOUNDED_PIECE_COMPOSITION.md) retains these guards through exact affine translation with sound values and exact domain. General nonlinear/uncertain-family operator closure remains missing; failed choices cannot be dropped. |
| §2.11 partial-operation image conversion | Covered common criterion and controls | [Injective partial-image transfer](PARTIAL_IMAGE_TRANSFER.md), root and reciprocal instances, finite-gap certificates. Exact image equality alone does not preserve universal definedness; arbitrary gap discovery and arbitrary operator closure are not proved. |
| §2.12 strict domains and sufficient properties | Covered common mathematical core | Strict finite-arity domain factorization, sufficient continuity/local constancy and certificate transport are proved. Full recursive property-description generation remains a proof task once its intended semantics is fixed. |
| §2.12 printed weak-tracking direction | Inconsistent under semantic-continuity reading | Constant/square masking counterexamples refute the proposed converse. A structural certificate interpretation is possible but is not automatically the source's intended repair; failure must remain inconclusive. |
| §§2.13–2.14 finite sets/variants | Covered explicit finite models; broader representation gaps | Exact guarded-piece compilation, mixed open boundaries, persistent coefficient witnesses, finite Hansen pointwise ranges and unbounded sets of finite coefficients are covered. Arbitrary bumpy/function representation and literal exceptional coefficient arithmetic are not obtained. General constructive demotion beyond supported pieces remains missing. |
| §2.15.1 cuts | Covered nonnegative construction/operations; proof gaps | Full signed construction and remaining source operation correspondence; strict/closed descriptions must not be identified structurally merely because they decode equally. |
| §2.15.2 Cauchy streams | Covered stated arithmetic slice | Rational-stream representation, arithmetic and representative independence with guarded division are proved. No generic computable real oracle is implied. |
| §§2.15.3, 2.15.6 digit streams | Covered normalized stream slices; proof gaps | All-real extraction/existence, carrying/place normalization and source online algorithm/delay claims remain distinct from summability and truncation estimates. |
| §2.15.4 continued fractions | Covered canonical and normalized finite correspondence; broader gap | Actual canonical irrational convergence and finite reconstruction are covered. Arbitrary admissible infinite-stream reconstruction/uniqueness and generalized numerators remain outside the proven slice. |
| §2.15.5 interval streams / accuracy | Covered finite strict arithmetic grammar; proof gaps | Same-stream convergence and executable certified search are proved under computable-stream/containment premises. Remaining source operators and extraction obstructions require correspondence; no rate or arbitrary-precision hardware implementation follows. |
| §§2.15.7–8 redundant/symbolic alternatives | Proof/specification gaps; some later-chapter research | Identify precise source proof-bearing conditions and algorithms before claiming redundancy, online or convergence advantages. Later performance narrative is not discharged by a finite example or a speed assertion. |

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
   source rule, with no guessed exceptional rows. Nearest-rounding/tie claims
   need the precise source convention before any proof is claimed.
2. **Family/operator closure (§§2.9–2.14).** Audit the printed operator and
   conversion claims against the generic same-witness family theorems, then
   discharge missing concrete premises for the source-supported families in one
   shared value/domain/property composition chain. Use the existing partial
   relations, guards, sets and tagged conversions. The present translation rule
   is one instance, not that chain's completion. Exit evidence must distinguish
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
