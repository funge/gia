# Thesis-to-formalization concordance

This is a reading map for Jeffrey Allen Tupper's *Graphing Equations with
Generalized Interval Arithmetic*, not a claim that the thesis has been fully
formalized. Start with the [project README](README.md), then use this document
to move between thesis ideas, Lean statements, and known gaps.
The [floating-point gap map](FLOATING_POINT_ROADMAP.md) compares the initial
Tupper target with existing rounding contracts and separates later C refinement.

## Sources, status, and labels

The [author's contents](https://www.dgp.toronto.edu/~mooncake/thesis/node1.html)
and selected original PDF pages were checked during the earlier formalization.
Public originals: [1996 thesis](https://www.dgp.toronto.edu/~mooncake/thesis.pdf)
and [2001 SIGGRAPH paper](https://www.dgp.toronto.edu/papers/jtupper_SIGGRAPH2001.pdf).
Those earlier visual checks used authorized private repository copies; PDFs and
Markdown transcriptions are not bundled here and are not build dependencies.
The transcription was damaged in places, so the PDF is authoritative. Existing
section/page labels preserve the checked source locations. Historical access
failures and validation receipts below describe the original environment, not a
requirement to access the private graphing repository. The migration changes
citation destinations, not claims of fresh source or URL availability checks.

Earlier work used a 105-entry technique inventory (historical private project record; not bundled)
and September 23 source-led review (historical private project record; not bundled)
as the starting point for locating techniques and source passages. This concordance
adds Lean proof status and translation obligations; it does not replace or duplicate
those inventories. Their entry counts are not proof-completeness measures.

The thesis and paper are separate coverage tracks. Specific inspected pages and
transcription differences are recorded below. No blanket formula equivalence,
complete source review or numbered theorem correspondence is asserted. A Lean
theorem name is a repository declaration, not a source theorem number.

Coverage snapshot: source tree at #52, commit
`9efa154bd09e8a9a2198974da6aaf1e37102746c`. The merged baseline is through #43
(`8ce2199f6d2d72c0c47269d02b8e1f1aa8cde7f0`). Rows marked **Review** depend on
unmerged work in this checkout. The separate #44 guarded-simplification branch
is not included in this snapshot. Consult [REVIEW_STACK.md](REVIEW_STACK.md)
for dependency history; PR state and mathematical coverage are different facts.

Labels describe fidelity, not proof quality:

- **Exact example:** the identified elementary example is proved under the stated
  representation. This does not certify its surrounding section.
- **Restricted:** a proved instance or narrower semantic counterpart of a thesis
  idea. The representation or algorithm differs, or important cases are missing.
- **Conditional:** a result depends on explicit enclosure/domain premises rather
  than verifying the numerical implementation that would discharge them.
- **Extension:** project infrastructure or an exploratory connection motivated by
  the thesis, without an asserted direct thesis construction.
- **Missing:** no corresponding project implementation/proof is claimed.

## Chapter map

The actual chapters are 1 **Motivation**, 2 **Numbers**, 3 **Arithmetic**,
4 **Graphs**, and 5 **Conclusion**. Most current work belongs to restricted
chapter-2 foundations and their compositional consumers. Chapter 3's extensive
function-model construction remains largely open; chapter 4 has conservative
mathematical checkers, not a verified renderer. Chapter 1 supplies motivation,
and chapter 5 supplies research directions, not completed implementation goals.

### Chapter 2: numbers, representations, and domains

| Thesis location | Correspondence in this checkout | Fidelity and boundary |
| --- | --- | --- |
| §§2.1–2.4: underlying number systems | `ℚ` and `ℝ` are imported from Lean/mathlib. [Intervals.lean](Intervals.lean) defines finite ordered rational endpoints interpreted over reals. | **Restricted / library foundation.** No reconstruction of the thesis's number-system development; no complex interval arithmetic. |
| [§2.5.3 Rounding](https://www.dgp.toronto.edu/~mooncake/thesis/node23.html), §2.10 | [RoundedAddition.lean](RoundedAddition.lean): `rounded_add_encloses`; [EvaluatorRounding.lean](EvaluatorRounding.lean): `directedBackend_sound`. | **Conditional.** Downward/upward enclosure inequalities are premises. No IEEE format, closest-representable rounding, NaN, infinity, signed-zero, overflow or subnormal implementation proof. |
| [§2.7.3 Inclusion Property](https://www.dgp.toronto.edu/~mooncake/thesis/node32.html), §§2.7–2.8 | [IntervalOps.lean](IntervalOps.lean): `mul_encloses`, `recip_encloses`; [Evaluator.lean](Evaluator.lean): `eval_sound`. | **Restricted.** Finite rational interval operations and an arithmetic AST satisfy real containment. Reciprocal needs a zero-excluding denominator; no full extended-real interval system or general optimal interval extension. |
| [§2.9.3 Linear Intervals](https://www.dgp.toronto.edu/~mooncake/thesis/node39.html) | [LinearIntervals.lean](LinearIntervals.lean): `QAffine`, `LinearInterval`, `linear_ordered`, `linear_hull_encloses`. | **Restricted.** One shared parameter in [0,1], rational affine bounds, real values. Endpoint ordering implies ordering throughout. No full real-coefficient or unbounded representation. |
| §2.9.3's explicit `x - x` example | `linear_exact_cancel` in [LinearIntervals.lean](LinearIntervals.lean); interpreter examples in [LinearEvaluatorExamples.lean](LinearEvaluatorExamples.lean). | **Exact example in our representation.** An exact shared affine input cancels to zero. This does not permit cancellation of independent values merely because they have equal interval descriptions. |
| §2.9.4 Constant Intervals, printed p.30 / PDF p.46 | `linear_constant_injective`, `linear_constant_hull`, operation equalities in [LinearIntervals.lean](LinearIntervals.lean) and [LinearMultiplication.lean](LinearMultiplication.lean); `evalLinear_constant_correspondence`. | **Restricted counterpart.** Exact finite-rational embedding and preservation of concrete +, −, × policies. Not the universal interval-extension or floating-point homomorphism. |
| [§2.9.6 Multi-Dimensional Linear Intervals](https://www.dgp.toronto.edu/~mooncake/thesis/node42.html) | [ParameterRestriction.lean](ParameterRestriction.lean): `affine_reparam_value`, `linear_reparam_contains`; **Review:** [AffineDomainGuards.lean](AffineDomainGuards.lean). | **Restricted / mostly missing.** Reparameterization handles one parameter. Two-coordinate affine domain guards are not a multidimensional interval bound representation; a general k-parameter arithmetic is missing. |
| §§2.9.5, 2.9.7–2.9.8: richer bounds | [PartialEnclosures.lean](PartialEnclosures.lean) has abstract `FunctionalBounds`. [LinearMultiplication.lean](LinearMultiplication.lean) bounds an intermediate quadratic product. | **Restricted.** Arbitrary real functions in a semantic contract are not an executable functional/symbolic interval system. A quadratic intermediate is not a quadratic-interval API. General higher-order bound families are missing. |
| [§2.11 Interval Function Domains](https://www.dgp.toronto.edu/~mooncake/thesis/node46.html) | [PartialEnclosures.lean](PartialEnclosures.lean): `DomainBounds`, `PartialEnclosure.Sound`, `domain_absent`, `domain_definite`, `collapsed_bounds_absent`. | **Restricted abstraction.** Definite/possible predicates separate domain facts from value bounds. They are not a literal encoding of Tupper's numeric domain interval and constraint representation. |
| [§2.11.4 Conjunctions](https://www.dgp.toronto.edu/~mooncake/thesis/node50.html) | Domain intersection and `partial_add_sound`; **Review:** [AffineDomainGuards.lean](AffineDomainGuards.lean), `affine_sum_defined_iff`, `affine_sum_append_defined`. | **Restricted.** The reviewed reciprocal-sum family has an exact common-environment conjunction of nonzero affine guards. This is not extraction for arbitrary syntax or existential feasibility over a region. |
| [§2.12 Property Tracking](https://www.dgp.toronto.edu/~mooncake/thesis/node52.html) | [SemanticContinuity.lean](SemanticContinuity.lean): `expr_continuousOn_of_defined`; [ConditionalContinuity.lean](ConditionalContinuity.lean): `conditional_threshold_certificate`. | **Restricted.** Specific definedness/continuity implications, with branch-boundary premises. No general implementation of the thesis's recursively weakly/strongly checkable property framework. |
| [§2.13 Interval Sets](https://www.dgp.toronto.edu/~mooncake/thesis/node56.html) | [FiniteLinearCovers.lean](FiniteLinearCovers.lean): `FiniteLinearCover`, `cover_excludes_zero`; [CoverArithmetic.lean](CoverArithmetic.lean): `cover_mul_sound`. | **Restricted.** Finite lists of bounded one-parameter intervals use existential membership. `no_finite_cover_of_unbounded_below` proves a genuine representation limit. This does not implement all set-valued/extended-real models. |
| §2.6 and §§2.14–2.15 | No project counterparts for extended/hyperreal arithmetic or the alternative real representations surveyed there. | **Missing.** Using mathlib reals is not a formalization of those constructions. |

### Chapter 3: arithmetic and partial functions

| Thesis location | Correspondence in this checkout | Fidelity and boundary |
| --- | --- | --- |
| §3.1: numerical function implementations | The conditional backend contracts above. | **Conditional / missing implementation.** No certified platform math library, argument reduction, ULP error analysis, or concrete directed-rounding implementation. |
| §3.2: constant-interval models | [Intervals.lean](Intervals.lean), [IntervalOps.lean](IntervalOps.lean), and [Evaluator.lean](Evaluator.lean) compose rational constants, coordinates, +, −, × and guarded ÷. | **Restricted.** Containment proofs for this fragment, not the chapter's model-construction charts, general optimality arguments, or unary/transcendental catalogue. |
| [§3.3.7 Linear Functions](https://www.dgp.toronto.edu/~mooncake/thesis/node113.html), [§3.3.24 binary examples](https://www.dgp.toronto.edu/~mooncake/thesis/node130.html) | `linear_add_encloses`, `linear_sub_encloses`; [LinearMultiplication.lean](LinearMultiplication.lean): `affine_product_identity`, `affine_product_encloses`, `linear_mul_encloses`. | **Restricted.** Exact affine operations and a proved product enclosure. The product uses a bounded `t*(1-t)` remainder; equivalence to the thesis's displayed two-step/one-step algorithms is not claimed. No general optimality theorem. |
| [§3.3.16 Partial Functions](https://www.dgp.toronto.edu/~mooncake/thesis/node122.html), [§3.3.27 Partial Binary Functions](https://www.dgp.toronto.edu/~mooncake/thesis/node133.html) | [LinearDivision.lean](LinearDivision.lean), [GuardedEvaluator.lean](GuardedEvaluator.lean), [DomainEvaluator.lean](DomainEvaluator.lean). **Review:** [QuotientDomains.lean](QuotientDomains.lean) and [PointDomains.lean](PointDomains.lean). | **Restricted.** Guards and relational contracts preserve actual partial values. Whole-hull reciprocal guards are conservative. Reviewed domain inference covers an outer quotient and complete exact rational singleton evaluation, not general uncertain-input inference. |
| §§3.2.18–3.2.21, §§3.3.18–3.3.21: discontinuous/piecewise cases | [PiecewiseSelection.lean](PiecewiseSelection.lean), [ConditionalEvaluator.lean](ConditionalEvaluator.lean), [ConditionalCovers.lean](ConditionalCovers.lean). | **Restricted.** Explicit branch semantics, lazy certified selection, and finite branch covers. Unknown guards can require both branches; no general automatic piecewise model construction or implication of continuity across jumps. |
| §3.4: polynomial interval arithmetic | [LinearEvaluator.lean](LinearEvaluator.lean) evaluates polynomial expressions using linear bounds. | **Missing representation.** Polynomial expression syntax is not polynomial interval arithmetic: no general polynomial-bound datatype or the chapter's construction/optimality results. |

### Chapter 4: graphing consumers and optimizations

| Thesis location | Correspondence in this checkout | Fidelity and boundary |
| --- | --- | --- |
| [§4.2.3 Pixel Testing](https://www.dgp.toronto.edu/~mooncake/thesis/node153.html) | [Evaluator.lean](Evaluator.lean): `eval_empty_pixel`; [PresenceChecker.lean](PresenceChecker.lean): sound `empty`, `present`, `unknown` outcomes. | **Restricted.** Zero sets of partial arithmetic expressions in rational boxes. No complete relation/Boolean specification language, pixel rasterization, screen mapping, or app correctness proof. |
| [§4.2.5 Exhaustive Subpixel Testing](https://www.dgp.toronto.edu/~mooncake/thesis/node155.html) | [Subdivision.lean](Subdivision.lean): `split_cover`, `subdivide_sound`, `refineBox_empty`, `refineBox_present`. | **Restricted.** Closed-box coverage and bounded refinement preserve sound outcomes. Exhaustion remains unknown, not absence; no convergence or complete decision procedure. |
| [§4.2.6 Continuity-Based Testing](https://www.dgp.toronto.edu/~mooncake/thesis/node156.html) | [Presence.lean](Presence.lean): `certified_curve_zero`, `segment_presence`; [ExpressionContinuity.lean](ExpressionContinuity.lean): `evaluator_segment_presence`. | **Restricted, direct mathematical counterpart.** Intermediate-value reasoning with actual defined values throughout a continuous segment. No verified rendering statistics, sampling probabilities, or completeness for tangencies. |
| §4.2.6 consumer, with domain-aware extension | **Review:** [AffineSegmentDomains.lean](AffineSegmentDomains.lean): `affine_segment_defined`, `certifyAffineSegment_sound`. | **Extension.** Affine denominator endpoint signs certify a safe common-coordinate segment even with poles elsewhere in the box. No arbitrary external-domain path certificate. |
| §4.5 [Optimization: Removing Conditionals](https://www.dgp.toronto.edu/~mooncake/thesis/node166.html) | [ConditionalArithmetic.lean](ConditionalArithmetic.lean): `arithmeticTree_value_iff`; branch selection in [ConditionalEvaluator.lean](ConditionalEvaluator.lean). | **Related prerequisite, not the optimization.** Exact partial-semantic distribution through branches is proved. The thesis discusses evaluation-case reuse, specialized compound operators, and rounding-control optimization; these are not implemented here. |
| §§4.1, 4.2.7–4.2.8, 4.3–4.4, 4.6–4.8 | Mathematical box/cell consumers only. | **Missing as complete systems.** No end-to-end renderer, caching optimizer, verified cutting heuristic, full comparison of alternative formalisms, or reproduced rendering suite. |

## Project foundations and experiments without a direct thesis theorem claim

These support the formalization but should not be counted as additional completed
thesis sections:

- [CellContinuity.lean](CellContinuity.lean) glues continuous local representatives
  only with coverage and agreement across overlaps. [CellCoverage.lean](CellCoverage.lean)
  and [AdaptiveCellCertification.lean](AdaptiveCellCertification.lean) prove
  coverage, definedness and continuity for successful bounded checks. Call bounds
  count evaluator invocations, not machine time or arithmetic complexity.
- **Review:** [tests/UncertainDomains.lean](tests/UncertainDomains.lean) distinguishes
  shared input witnesses from independently projected operand witnesses and shows
  the finite-cover limitation at a pole. [tests/OptionalRangePrototype.lean](tests/OptionalRangePrototype.lean)
  is a test-only experiment separating unavailable range information from domain
  information; it is not an adopted production representation.
- [AuditPolicy.lean](AuditPolicy.lean) and [AUDIT_POLICY.md](AUDIT_POLICY.md) enforce
  proof-dependency policy. This is verification infrastructure, not interval theory.

## Assumptions and interpretation rules

A named theorem is kernel-checked under its stated hypotheses and the recorded
axiom policy. It does not discharge every hypothesis for every expression.
In particular:

1. `Value` requires a nonzero divisor. `Expr.realValue` is a total representative;
   it is used as the partial value only after definedness is established.
2. `BackendSound` and directed-rounding inequalities are explicit contracts.
   IEEE 754 supplies the intended rounding directions, not a verified concrete
   format or implementation in this project.
3. Arbitrary domain predicates and coordinate relations may be supplied by a
   caller. `PartialEnclosure.Sound` includes both range containment and domain
   implications. Dropping its existence obligation would change the meaning.
4. Same-environment expression witnesses are not interchangeable with independent
   operand witnesses. Bounds can lose correlation without making the theorem false.
5. General evaluator failure means inconclusive. **Review:** `eval_point_defined_iff`
   in [PointDomains.lean](PointDomains.lean) proves the narrower exception: the exact
   backend at rational singleton coordinates succeeds iff a partial value exists.
   Only there does failure certify arithmetic undefinedness. External-domain
   uncertainty is still separate.
6. Continuity needs its premises on the whole relevant path/domain. Defined
   endpoints, opposite signs, or overlapping bounds alone cannot rule out a pole,
   jump, or external hole. The [segment controls](tests/AffineSegmentDomains.lean)
   include these distinctions.

## Reading and validation route

For a first worked correspondence, read §2.9.3 alongside `linear_exact_cancel`.
Then read §2.11 alongside `PartialEnclosure.Sound`, followed by §4.2.6 alongside
`segment_presence`. For the reviewed integration, follow
[the affine segment example and scope](GENERALIZED_INTERVALS.md#affine-domain-certificates-along-segments)
and its independent fixture. The example is project-authored, not claimed to
reproduce one of the thesis's figures.

Use the [pinned setup](README.md#reproducible-setup), then run `./check.sh` from
this directory. [VALIDATION.md](VALIDATION.md) records actual builds and audits;
this concordance is a source-assessed map, not a new proof or independent Lean
kernel validation. Local links and cited declaration names should be checked
whenever entries change. Keep per-run counts in the validation log.

## Roadmap to Lean versions of the thesis proofs

The goal is to formalize the actual results and arguments, chapter by chapter
where practical. A topic match is not completion. For each selected result,
record the displayed source statement, variable domains, every hypothesis,
conclusion, and proof steps before assigning an exact-counterpart label. State
any change of representation explicitly, and prove a translation lemma when
needed. Keep the source argument identifiable even if Lean uses a shorter
library lemma for one step.

| Order | Source target and comparison obligation | Reusable dependencies | Work still required |
| --- | --- | --- | --- |
| 1: chapter 2 | §2.7.3: compare the unary/binary inclusion quantifiers with `eval_sound`. Our theorem assumes actual partial `Value`, enclosed coordinates, `BackendSound`, and successful evaluation, and concludes containment. | `QInterval.Contains`, `Value`, `mul_encloses`, `recip_encloses`, `eval_sound`. | The unary/binary/n-ary quantifiers are now visually checked on printed p.24 (PDF p.40); construct the representation/model translation and distinguish partial-operation guards and finite-endpoint restrictions. An operational evaluator theorem is not automatically the same statement as a model inclusion definition. |
| 2: chapter 2 | §2.9.3: compare its non-collapsing affine-bound condition and cancellation calculation. Our `affine_order` assumes order at endpoints 0 and 1 and concludes order for a parameter in [0,1]; `linear_exact_cancel` states containment in the self-difference of an exact affine interval iff the result is zero. | Real ordered-ring facts; `QAffine.value`, `affine_order`, `linear_exact_cancel`. | The original inequalities and cancellation calculation are now visually checked on printed pp.28–29 (PDF pp.44–45). The finite-rational translation and non-collapsing equivalence are now proved in LinearIntervals (see the subsequent correspondence below). Extended-real coefficients and the full source representation remain outside that result. |
| 3: chapter 2 | §2.11: compare Tupper's concrete domain description and inclusion conditions with the three obligations of `PartialEnclosure.Sound`. | `domain_absent`, `domain_definite`, `restrict_sound`; reviewed shared-environment controls. | The PDF p.50 condition uses three-valued equivalence with optimistic projection, not the Markdown implication. Define that source semantics and its universal input quantification before comparing the abstract contract. Predicate abstraction alone does not prove equivalence to the numeric description. General conjunction projection must retain common witnesses. |
| 4: chapter 3 | §3.3.7, then one explicitly selected binary model in §§3.3.22–3.3.26. Compare derivative/sign hypotheses, chosen bounds and the argument establishing validity or optimality. | Affine ordering and interpolation; existing product-containment lemmas only where their statements match. | Read the displayed charts/formulas and reproduce the selected derivation. Do not substitute our bounded quadratic remainder argument and call it Tupper's proof. Broader function libraries follow only after this first precise model. |
| 5: chapter 4 | §4.2.6: compare the source's rendering predicate and continuity/sign premises with `segment_presence`. Our result requires a continuous representative and actual values on the entire segment, certified endpoint bounds, and endpoints inside the box; it concludes an actual zero in that box. | Mathlib intermediate value theorem, `certified_curve_zero`, `segment_mem`, semantic continuity. | Define the source rendering predicate or explicitly restrict it to arithmetic zero sets, then prove the translation and compare boundary conventions. Only after that should this count as a Lean version of the full source claim. |

Chapter 1 remains explanatory context. Chapter 5 is a source of future goals,
not an extra block of already formalized theorems. The ordering above is a proof
roadmap, not permission to introduce a new floating-point model or rewrite the
existing interfaces.

### Historical source-access limitations before repository copies

On 2026-11-07, the readable HTML sections were available through the web tool,
but direct GIF equation retrieval was unsupported there. Chromium navigation to
§2.9.3 failed with a DNS error. A normal proxied request to the author's
`img408.gif` returned HTTP 403 at CONNECT; no image was downloaded and no bypass
was attempted. A subsequent authorized web-tool check opened the official PDF
as 173 pages and accepted screenshot requests for zero-based pages 0 and 80
using the returned PDF reference. However, this thread's tool wrapper delivered
only citation strings, without image content or image bytes. Successful screenshot
requests therefore did not establish visual inspection here. The remaining
obstacle is image delivery, not a claim that the official PDF is unavailable.
At that time, rendered pages or a permitted local copy were needed for precise
comparison. The repository-copy review below supersedes this availability limit
for its explicitly inspected pages; uninspected statements remain unqualified.

## Highest-value remaining thesis work

The map suggests three substantial gaps, not automatic implementation commitments:

- Define a faithful, executable multidimensional value/domain representation
  before claiming general §2.9.6 or §2.11 coverage. Shared-witness constraints,
  uncertain ranges and unbounded poles need distinct treatment.
- Formalize a specific chapter-3 model-construction rule, including its hypotheses
  and precision claim, rather than treating another arithmetic AST constructor
  as coverage of the chapter's modelling machinery.
- Connect domain and continuity certificates to richer consumers while retaining
  path-wide obligations. A complete renderer or verified optimizer would require
  additional semantics and implementation verification.

These fit the distinction in [§5.3 Future Work](https://www.dgp.toronto.edu/~mooncake/thesis/node178.html)
between generalized arithmetic research, generated implementations, and wider
applications. None is reported here as completed, and floating-point machinery
would require a separate scope decision.

### Subsequent project result: restricted segment-domain completeness

After the #52 source snapshot, the `AffineSegmentDomains` module adds
`affine_segment_safe_iff_defined` and `affine_segment_unsafe_iff_hole`. They
characterize an existing restricted Boolean test, using its affine interpolation
lemma and mathlib's intermediate value theorem. This is an **Extension**, not
an upgrade of any exact-thesis correspondence above. It requires no unavailable
source formulas and does not resolve their comparison obligations. See the
[current semantic scope](GENERALIZED_INTERVALS.md#completeness-of-the-restricted-segment-domain-test).

A further project integration retains the path witness of the affine presence
certificate and transports it into a caller-specified external domain only under
whole-path inclusion. Restricted absence needs no such premise. This remains an
**Extension**: it does not discharge the source-comparison obligations above or
implement a general external-domain solver. See the
[external-domain contract](GENERALIZED_INTERVALS.md#presence-and-absence-under-external-domain-restrictions).

`AffineRegions` subsequently checks a restricted class of external domain
conjunctions: closed rational affine half-spaces on one supplied segment. It uses
affine convexity to discharge the existing path premise and preserves unknown
for unresolved constraints. This is an **Extension** related to domain conjunctions,
not a formalization of Tupper's full numeric domain representation or a general
multidimensional interval model. Its exact statement concerns the project's
explicit constraint-list semantics; original-equation caveats remain unchanged.

`AffineRegionSearch` connects this region checker to the existing finite sampling
policy and arithmetic zero-exclusion certificates. As a project **Extension**,
it supplies restricted root soundness but no exhaustive-search or convergence
claim and no new exact correspondence to the thesis's sampling algorithms.
Rejected paths do not certify box absence; an admissible root can be missed when
all automatic candidates share an inadmissible or undefined center.


`AffineRegionSubdivision` reuses the project's alternating midpoint refinement
with the constrained checker. This **Extension** is related to chapter 4's
subpixel testing and continuity approach (sections 4.2.5–4.2.6), but is not claimed
to reproduce an inspected thesis algorithm or theorem. It proves restricted-root
soundness through exact closed-child coverage and demonstrates a missed root
recovered at finite depth. It does not prove eventual detection, solve arbitrary
external domains, or alter the outstanding source-comparison obligations.


## Repository-source verification update (2026-11-07)

Primary source: [repository thesis PDF](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=40).
Secondary navigation: source-review ledger (historical private project record; not bundled).

This is a targeted review, not certification of either Markdown transcription.
Thesis printed pages use PDF page = printed page + 16. Visually inspected here:
contents PDF pp.7–8; body PDF pp.36, 40, 43–46, 50–53. Paper PDF pp.1, 6–7
were inspected. Rendering succeeded locally; the paper renderer emitted ICC
colour-profile warnings, which did not prevent these pages from being read.
The repository's technique inventory and source-review ledger were consulted as
secondary navigation aids; their wider inspection claims are not repeated as ours.

| Source | Verified content | Consequence for this formalization |
| --- | --- | --- |
| Thesis §2.7.3, printed p.24 / PDF p.40 | Unary, binary and n-ary inclusion quantify over represented input values and require output containment. | Existing containment results remain restricted instances. An evaluator that can return unknown is not by itself a total source model. |
| Thesis §2.9.3, printed pp.28–29 / PDF pp.44–45 | Affine bounds use coefficient form, must be ordered and defined throughout [0,1]; the x−x example returns zero for exact affine bounds. | Endpoint-based QAffine needs an explicit translation and order equivalence. Finite rational endpoints remain narrower than the source's extended-real coefficients. |
| Thesis §2.9.3 continuation, printed p.30 / PDF p.46 | There is no generally best affine demotion independent of later use. | Do not advertise a universal optimal linear enclosure or infer optimality from containment. |
| Thesis §2.11.1, printed p.34 / PDF p.50 | Domain validity uses a three-valued equivalence between actual definedness and the domain classification, followed by optimistic Boolean projection. | Markdown's one-way implication is not faithful. A source adapter must account for both directions and all represented input values. |
| Thesis §2.11.2, printed p.35 / PDF p.51 | Downward and upward domain demotions act on the respective endpoint, preserving the three-valued classification information order. | The Markdown's demotion of the whole endpoint pair obscures the original endpoint-specific formulas. Transcribe from the PDF when formalizing them. |
| Thesis §§2.11.4–2.12.1, printed pp.35–37 / PDF pp.51–53 | Domain constraints are conjoined; definedness, continuity and local constancy have distinct recursive property contracts. | Our domain intersections and selected continuity results do not implement the full property calculus. Do not silently reverse or strengthen its displayed implications. |

A significant comparison obligation is now explicit: PartialEnclosure.Sound has
`definite p → ∃ z, R p z`. That existential obligation alone does not establish
the source's domain assertion for every represented input tuple. For example,
existence of a reciprocal value for input 1 does not establish definedness for
input 0 when both are possible. This is a difference in contracts, not a discovered
unsoundness in the proved project contract. Any exact correspondence needs a
precise input-indexed interpretation and proof, rather than relabelling the
current abstraction as the thesis encoding.

The roadmap reuses the existing inventory identifiers:

| Existing entry | Lean-specific next obligation |
| --- | --- |
| F03 (inclusion), F14 (Boolean demotion) | Translate the inspected model/value and property contracts; keep optimistic truth distinct from a witness. |
| F06 (parameterized bounds) | Prove the coefficient/endpoint correspondence and finite-rational non-collapsing equivalence. |
| F08/F15 (domains), F09 (properties) | Make the input quantifiers and definite/possible interpretation explicit before claiming source equivalence. |
| L05 (linear operations) | Inspect its chapter-3 formula-level premises next; containment alone is not a proof of the source construction. |
| R08 (per-piece metadata), R09/R10 (branch identity/encoding) | Keep the paper track separate and discharge label-soundness/site-identity obligations before implementation claims. |

The next bounded thesis proof target can now be specified from the original:
translate finite rational coefficient bounds `a+b*t` into QAffine endpoints
`(a,a+b)`, and prove that ordering at 0 and 1 is equivalent to ordering throughout
[0,1]. Relate that translation to the inspected cancellation example. This
addresses the existing chapter-2 roadmap without new FP assumptions, new search
interfaces, or a claim about extended-real coefficients. Chapter-3 construction
charts still require their own formula-level inspection.

## Separate 2001 paper track

Primary source: [repository paper PDF](https://www.dgp.toronto.edu/papers/jtupper_SIGGRAPH2001.pdf#page=6).
Secondary navigation: inventory entries R09–R10 (historical private project record; not bundled).

The paper is *Reliable Two-Dimensional Graphing Methods for Mathematical Formulae
with Two Free Variables*, not a later edition of the thesis. On PDF p.1 the author
explicitly excepts branch-cut tracking from the methods he says were implemented
in 1992 and demonstrated in 1993, and refers to the 1996 thesis for more detail on
other methods. This supports tracking §12 separately; it does not establish that
every detail in the paper first appeared in 2001.

| Paper location, visually checked | Project relationship | Status |
| --- | --- | --- |
| §11, PDF p.6: interval sets and per-element domain/continuity properties | FiniteLinearCover supplies finite unions and domain soundness, but uses bounded one-parameter components with different contracts. | Restricted relationship; not Algorithm 3.1 equivalence. |
| §12, PDF pp.6–7: branch sites, partial maps from sites to choices, compatible unions | Existing shared-environment semantics, threshold guards and finite covers do not carry these per-component site maps or filter their Cartesian products by map consistency. | Missing paper mechanism; not already implemented by conditional branches. |
| §12, PDF p.7: cut/chosen bit fields and masked equality | No corresponding bit-field implementation or machine proof exists here. | Missing optimization, separate from abstract compatibility. |
| §12, PDF p.7: sharing equivalent cut sites | Existing algebraic equivalence proofs do not implement site assignment/common-subexpression preprocessing. | Missing semantic identification pass. |

The checked compatibility formula sets `m = g.cut AND G.cut` and compares
`g.chosen AND m` with `G.chosen AND m`. Abstractly, shared site assignments must
agree; absent assignments impose no constraint and a compatible result carries
the union. The checked floor pseudocode preserves labels when it does not split
and adds site choices 0/1 in its two-piece split. The example separates repeated
uses of the same floor from unrelated alternatives. Labels preserve discrete
choice correlation; they do not recover all continuous dependence or prove
continuity across a discontinuity.

A future bounded paper milestone could prove finite partial-map compatibility
and that compatible-pair filtering preserves every concrete shared-environment
witness, provided the labels are sound for that witness. Before claiming the
paper algorithm, also prove sound labels for a selected splitting primitive and
justify common-subexpression site identity. Arbitrarily equal numeric ranges do
not justify a shared site. General site preprocessing, floor syntax, bit fields
and a full rendering algorithm are separate scope decisions; none is added here.


## Subsequent proof: finite-rational affine correspondence

Following the repository-source review and inventory F06, `LinearIntervals.lean`
now proves both coefficient/endpoint round trips, real-value equality,
`affine_order_iff`, `affine_coefficients_order_iff`,
`linear_coefficients_realizable_iff`, and `linear_coefficients_contains`.
These match the inspected coefficient semantics and non-collapsing condition
of §2.9.3, printed pp.28–29/PDF pp.44–45, restricted to finite rational
coefficients. The endpoint criterion is a proved characterization of that
restricted condition, not an attributed separately numbered thesis theorem.

The [independent fixture](tests/AffineCorrespondence.lean) connects the translated
exact input to `evalLinear`, proves zero containment and its exact zero set,
and contrasts ordinary constant-interval subtraction. Counterexamples delimit
parameter-domain, affine-form and exact-input requirements. See the
[precise scope](GENERALIZED_INTERVALS.md#finite-rational-correspondence-with-thesis-coefficient-bounds).
The earlier source-review paragraph proposing this target is historical context;
this result discharges its finite-rational correspondence obligation only.
No source claim about extended-real coefficients, demotion optimality, paper
branch-cut tracking or IEEE implementation is upgraded.


## Subsequent proof: constant-interval embedding

The next chapter-ordered step follows inventory F06 and the visually inspected
[§2.9.4, printed p.30 / PDF p.46](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=46).
The source's map has zero slopes. The existing constant constructor is now
proved injective using hull as a left inverse, with exact coefficient identity,
pointwise membership preservation, and commutation with the current finite
rational +, − and × operations. A success-conditioned interpreter theorem
composes those equalities. The [fresh fixture](tests/ConstantEmbedding.lean)
checks concrete mixed-sign composition and counterexamples to stronger claims.

This completes a **restricted counterpart** of the map and selected operation
preservation, not the source's claim for arbitrary operators defined by interval
extension. No general interval-extension optimality theorem, infinite endpoint
case, floating-point embedding or unrestricted interpreter equivalence is
asserted. See [the detailed scope](GENERALIZED_INTERVALS.md#constant-interval-embedding-from-thesis-section-294).

### Subsequent bridge: quadratic coefficient bounds

Following §2.9.4, thesis §2.9.5 (printed p.30,
[repository PDF p.46](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=46))
introduces quadratic bounds and postpones demotion. Inventory F07 is the
starting record. The original page was visually checked: coefficients are
extended real, and well-definedness is required. The current finite-real
polynomial result is narrower and automatically total.

`affine_product_quadratic` identifies the exact coefficient representation of
existing affine products. `quadratic_chord_lower_iff` and
`quadratic_chord_upper_iff` characterize necessary and sufficient constant
corrections to the endpoint chord. These reuse the existing bubble bound and
explain the current multiplication policy; they are derived results, not a
claim that §2.9.5 contains these proofs. See the
[scope and counterexamples](GENERALIZED_INTERVALS.md#quadratic-bounds-and-fixed-chord-corrections).
No complete quadratic interval type, extended-real validity test, unrestricted
optimal affine demotion or later chapter-3 algorithm is formalized here.
SIGGRAPH §5 (repository PDF p.3, visually checked) concerns ordinary interval
enclosure and supplies no counterpart
to this coefficient construction. The paper's domain and branch-cut contracts
remain separate obligations.

### Subsequent proof: two independent affine parameters

Source: thesis §2.9.6, printed pp.30–31/PDF pp.46–47, and §2.9.7's
non-collapse condition on printed p.31/PDF p.47. Both original pages were
visually checked at graphing commit `18f2e0e22a4a5a7893a87252bd0722c919d9a546`,
starting from inventory F06/F07. The source permits independent parameters and
extended-real coefficients; this result specializes to two parameters and
finite rational affine coefficients.

`affine_form_square_order_iff` in [AffineDomainGuards.lean](AffineDomainGuards.lean)
proves that all four corner comparisons are necessary and sufficient for the
source's whole-square ordering condition. The executable `affineSquareOrdered`
is certified by `affine_square_ordered_iff`; `affine_square_fibers_iff` links it
to nonempty fibers of existing FunctionalBounds. The corner characterization
is derived here, not attributed to a numbered theorem in the source. See
[scope and controls](GENERALIZED_INTERVALS.md#two-independent-affine-parameters).

No arbitrary-dimensional representation, extended-real validity, generalized
operator library, FP conversion or source-wide equivalence is claimed. The
paper's §5 ordinary enclosure and §8 domain tracking are related contracts;
its §12 discrete branch-choice correlation is a different construction.
In particular, identifying independent parameters with one another is not
licensed by either our proof or the source's shared-parameter convention.

### Chapter-2 milestone: universal input-domain semantics

The earlier input-quantifier obligation now has a restricted formal bridge in
[UniversalDomains.lean](UniversalDomains.lean). Source navigation used inventory
F08/F15 and the existing ledger; thesis §§2.11.1–2.11.2, printed pp.34–35/PDF
pp.50–51, were visually rechecked. The PDF's optimistic three-valued equivalence
is authoritative over the damaged Markdown implication. SIGGRAPH §8 (original repository PDF p.4, visually checked) describes definite,
absent and uncertain cases that agree with this domain-information interpretation.

`UniversalSound` quantifies numerical enclosure and compatible definedness over
every admitted input witness. `universal_projects` precisely identifies the
nonempty-input assumption needed to recover existing existential Sound. The
logical `exactInputDomain` has universal lower and existential upper predicates;
`exact_input_domain_precision` proves their information extremality on nonempty
fibers. This is a propositional counterpart of the Boolean extrema, not numeric
infimum/supremum machinery or an executable domain solver. The empty-fiber
convention is explicit and is not asserted to match the source's convention.

Same-input addition, external restriction, and the existing guarded evaluator
are integrated. A reciprocal example distinguishes mixed defined/undefined
inputs from one successful witness; empty-input and incompatible-witness controls
prevent vacuous or independently projected composition. See
[full scope](GENERALIZED_INTERVALS.md#universal-input-domain-semantics).

The source's full three-valued algebra, extended-real/λ value rules, domain
representation/demotion operators and subsequent property calculus are not
formalized by this layer. Sections 2.9.8 and 2.10 remain documented gaps rather
than being claimed complete on the way to this domain milestone. No new FP
assumptions are introduced; no source-wide model equivalence is asserted.

### Concrete domain-model milestone: partial square root

Thesis §2.11.5 (printed p.36/PDF p.52) and SIGGRAPH §8 (PDF p.4) were visually
checked. [SquareRootDomains.lean](SquareRootDomains.lean) proves universal
soundness and all three cases of an exact-real counterpart of the paper's
SquareRoot algorithm: absent on entirely negative ranges, unchanged incoming
domain on ordered nonnegative ranges, uncertain on mixed ranges unless already
absent. Numeric endpoints use exact real square roots, replacing the paper's
rounded endpoint operations; no IEEE execution claim is made.

The original thesis's final decorated example prints [-1,-1] with a mixed-range
output [0,1] and uncertain domain. This is loose but sound: uncertain
definedness permits undefinedness, and containment is vacuous when there is no
value. A typo is plausible given the preceding [-1,1] example, but is not
established. The printed result differs from the paper algorithm's precise
absent classification. The paper's unambiguous branches justify
the [-1,1] regression. The thesis's negative infinite payload is also different
from the paper's retained payload; only the absent-domain conclusion is common.

The new operation composes through the universal input-domain contract with
existing guarded evaluation, addition and restrictions. Its partial value
relation excludes negative inputs explicitly. This is not Expr syntax, a
computable exact solver, a rational sqrt implementation, or a proof of rounded
sqrt behavior. See [scope and source discrepancy](GENERALIZED_INTERVALS.md#square-root-with-domain-tracking).
The chapter-2 property calculus remains a separate open milestone.

### Property-tracking specification obstruction

Inventory F09 and its source-review ledger led to thesis §2.12, printed
pp.36–37/PDF pp.52–53, checked in the original repository PDF. Page 36 defines
recursive weak checkability in the direction

`P(g ∘ h, x, b) → P(g, h(x), P(h, x, b))`.

Page 37 defines the continuity check as continuity of the operator at its
argument conjoined with the child flags, then states that continuity is weakly
checkable. Under the ordinary real, unary specialization these claims cannot
all hold without further qualifications. This is separate from the loose but
sound square-root example discussed above: here the flags are classical exact
continuity propositions, not uncertain interval flags.

[PropertyComposition.lean](tests/PropertyComposition.lean) makes the
specialization explicit: `CheckContinuous g x b := ContinuousAt g x ∧ b`.
It proves the reverse, sufficient direction using mathlib's composition theorem.
It then constructs a total real jump function and proves, via the intermediate
value theorem, that it is not continuous at some point of [0,1]. A constant
outer function yields a continuous composite with a true leaf flag, while the
printed recursive conclusion fails because the child is discontinuous. This
is a kernel-checked obstruction to the literal specialization, not a claim to
have formalized every source property convention or identified the author's
intended correction.

SIGGRAPH §10, original PDF p.5, was also visually checked. Its addition rule
uses the conjunction of lower continuity flags and an upper flag of true.
Thus failure to certify an operand's continuity need not assert discontinuity
of the result. This is consistent with the sufficient direction and the
existing inventory's warning about cancellation/constant compositions.
No paper addition or floor algorithm is claimed verified by this fixture.

**Decision before a generic property API:** either formalize the sufficient
composition direction under an explicitly corrected/separate specification,
or establish additional source hypotheses that resolve the printed direction.
Do not silently reverse the arrow or claim the literal theorem is proved.
Existing specific continuity and gluing theorems remain valid. No mathematical
production API is changed by this review; the fixture is registered in the
standard integration and axiom checks.

## Public-operation completeness track and finite basic operations

The [C-operation ledger](OPERATION_COVERAGE.md) complements this source roadmap:
it tracks each public symbol's mathematical result, evaluator integration and
remaining domain/C-refinement gap. Completing that ledger does not itself complete
the thesis, and existing mathlib functions are not counted as interval proofs.

The current [basic-operations milestone](BASIC_OPERATIONS.md) targets finite
rational negation, absolute value, min/max, hull and intersection. The original
repository PDF, printed p. 59 / PDF p. 75, was checked for the §3.2.13 negation
and §3.2.14 absolute-value examples. The client reproduces both with exact rational
constants. This is a narrower finite instance of the source's section-based
construction, not a proof of its full extended-real generic algorithm. Hull and
intersection are ordinary set-bound utilities; they do not implement branch-site
identity tracking. Build status is in the appended validation record.

### Attained monotone endpoints and integer rounding operations

[MonotoneIntegerBounds](MONOTONE_INTEGER_BOUNDS.md) formalizes the closed finite
ordinary-real case of the increasing/decreasing endpoint arguments in §§3.2.10–
3.2.11 and instantiates it for floor and ceiling (§3.2.13). The original PDF was
checked at printed pp. 56–58 / PDF pp. 72–74. The source floor example is a
regression. Least-interval proofs are derived consequences of attained endpoints;
they do not assert exact discrete images or continuity. Extended-real relations,
open endpoints, limits, C execution and evaluator integration remain outside scope.

### First executable hardware addition (conditional)

[Hardware addition](HARDWARE_ADDITION.md) follows the outward-addition contract
of §2.5.3 (printed p. 20), with compiled Lean invoking binary64 hardware through
a minimal C adapter. `HardwareAddition.assemble_encloses` proves enclosure
conditional on contracts for observed adapter results and their finite-value
interpretation. It does not prove IEEE bit semantics, FFI correspondence, the
existing C library, or §2.10 coefficient demotion. Unknown is retained for
nonfinite results. No toolchain or axiom-policy change was made.

### Source caution: asymmetric error labels in §3.1.4

Visually checked the pinned repository PDF at [printed pp. 46–47 / PDF pp. 62–63](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=62)
on 2026-11-08. Page 46 defines `−h₋ ≤ gF − gR ≤ h₊`, consistently with its prose.
Page 47 then subtracts `h₋` for the downward bound and adds `h₊` for the upward
bound. These formulas do not follow for general asymmetric error bounds.
Rearranging the stated premise instead gives `gF − h₊ ≤ gR ≤ gF + h₋`;
any rounding of those endpoint calculations must also be outward.

For example, `gF=2, gR=0, h₋=1, h₊=2` satisfies the premise, but the printed
lower calculation gives 1, above the true value 0. Conversely,
`gF=0, gR=2, h₋=2, h₊=1` satisfies it, but the printed upper calculation gives
1, below 2. All these small integers are exactly representable, so outward
rounding of these particular subtractions/additions does not repair the issue.
This is a mismatch in the original PDF, not just the Markdown transcription.

A future formalization should state the premise and use the algebraically valid
orientation, explicitly documenting the departure from the printed construction.
This observation is not a formal verification of the separate nearest-neighbor
example later on p. 47. The current hardware addition contract and proof do not
use these asymmetric-error formulas, and no new FP assumption is introduced here.

### Directed hardware subtraction

[HardwareSubtraction](HardwareSubtraction.lean) extends the finite conditional
hardware path with crossed endpoints. The C counterpart is `gi_interval_sub`;
[scope and priorities](HARDWARE_ADDITION.md#next-hardware-operation-subtraction)
link the implementation and the visually checked §3.2.22 (printed p. 64).
The source's real subtraction rewrite motivates the operation but is not used
as an unproved native-program equivalence: execution uses direct subtraction.
The explicit directed-operation contract, unknown-on-nonfinite policy and
unproved decoder/FFI boundary remain unchanged.

### Hardware four-corner multiplication

`HardwareMultiplication.assembleFour_encloses` connects the executable assembly
function to the rounded-corner proof, under four directed multiplication contracts
and the approved finite min/max contracts. Tupper §3.1.1 (printed p. 45 / PDF p. 61)
was visually checked and explicitly lists min/max as exact functions. The source
example `[-2,3] × [5,7] → [-14,21]` in §3.2.25 (printed p. 67 / PDF p. 83) is
reproduced by the semantic fixture and native interval operation. The four-corner
implementation does not claim the source's sign-section optimization or bit-level
IEEE/C correctness. See [scope and trust boundary](HARDWARE_MULTIPLICATION.md).

### Finite hardware division follow-on

[Guarded native division](HARDWARE_DIVISION.md) connects §2.5.3's directed arithmetic
and §3.2.22's reciprocal/multiplication reasoning to a four-quotient enclosure.
The guard proves nonzero denominators and excludes zero-containing intervals
conservatively. It is narrower than §3.2.26's generalized partial binary functions.
The adapter and finite ordering remain explicit contracts; this does not verify
C's reciprocal-then-multiply implementation or unbounded outputs.
