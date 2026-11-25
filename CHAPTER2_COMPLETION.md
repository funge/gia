# Chapter 2 completion criteria and dependency plan

**Chapter 2 is materially incomplete.** Passing a finite-model milestone does not
close the broader source section. This document defines the finish line; the
[coverage checklist](CHAPTER2_CHECKLIST.md) and [concordance](THESIS_CONCORDANCE.md)
retain the detailed existing evidence. The target is Tupper's mathematics, not
performance or C implementation verification. Hardware correspondence remains a
separate refinement layer under the existing explicit contract.

Sources: the author's [numbered contents](https://www.dgp.toronto.edu/~mooncake/thesis/node1.html)
and [thesis PDF](https://www.dgp.toronto.edu/~mooncake/thesis.pdf), with the source
checks already recorded in the concordance. This tranche additionally checked
§2.11.4 visually on printed pp.35–36 / PDF pp.51–52. This roadmap is not a claim
of a new line-by-line audit of every section. Any newly formalized formula must
be checked against the original PDF, not only the damaged transcription.

## Acceptance rule

A proof-bearing result is complete only when its source hypotheses, conclusion
and semantic conventions have a precise Lean counterpart, with supporting
imports/lemmas, edge controls, an enforced axiom audit and full project gate.
A restricted finite theorem stays labeled restricted. An assumed adapter contract
stays an assumption; empirical tests cannot discharge it. A source claim refuted
under a proposed interpretation must retain its counterexample and an explicit
resolution, not be silently repaired or marked proved.

For foundational or survey material, completion means a source-checked mapping
of its mathematical definitions/results to existing Lean/mathlib declarations,
with an explicit account of any unmatched conventions. It does not mean rebuilding
mathlib or implementing every surveyed real-number representation as a runtime.
An unmatched proof-bearing obligation cannot be closed merely as a survey.

## Original planning snapshot: section-by-section exit criteria

The rows and dependency sequence below preserve the initial planning snapshot;
references to open/local #32/#33 work are historical, not current PR status.
Use [the maintained closeout matrix and three-package program](CHAPTER2_CLOSEOUT.md)
for current evidence and remaining obligations. The acceptance rule above remains
in force.

| Section | Kind and current position | Required exit evidence |
| --- | --- | --- |
| 2.1 Integers | Mathlib-provided foundation; residue results are applications. | Map source arithmetic/order/conversion claims to `Int` definitions and proved library laws; identify any source-specific convention. |
| 2.2 Rational Numbers | Mathlib-provided `Rat` foundation used throughout. | Map normalized rational arithmetic, order and real embedding; do not confuse exact certificates with hardware runtime. |
| 2.3 Real Numbers | Mathlib-provided `Real`/analysis foundation. | Map the ordered-field/completeness properties actually used by the source; keep representation survey separate. |
| 2.4 Complex Numbers | Mathlib supplies complex arithmetic; current GIA values are real. | Record exact source-to-library correspondence and delimit any complex-valued interval claims; library availability alone is not a completed mapping. |
| 2.5 Floating Point | Exact finite binary64 decoding/order and conditional directed contracts exist. | Source-check rounding, order and exceptional arithmetic; prove model-level claims or name the approved assumptions precisely. Finite decoding is not the full source FP system or a native refinement proof. |
| 2.6 Extended Real Numbers | Unresolved convention/model bridge. | Specify the source hyperreal/type-conversion/infinity conventions faithfully and prove operation laws used later. Do not substitute mathlib extended reals without checking equivalence, or equate decode failure with infinity. |
| 2.7 Interval Arithmetic | Exact finite strict comparison, finite enclosure and bounded image hull exist. | Complete the source order/projections, inclusion and interval-extension statements with actual operand witnesses, applicable arity and exceptional-domain conventions; separate interval algebra identities from enclosure inequalities. |
| 2.8 Real Interval Arithmetic | Nonempty bounded closed hull is proved. | Close empty/unbounded/extended-endpoint obligations and source demotion correspondence, depending on 2.6; preserve unattained-boundary examples. |
| 2.9 Generalized Interval Arithmetic (1–8) | Shared-parameter finite affine instances, quadratic remainder facts, functional predicates; finite Boolean composition in #32. | A common family interpretation and exact correspondence for each claimed constant/linear/quadratic/multi-parameter/functional/symbolic instance, plus Boolean projections/composition scope. Existing one-parameter affine and polynomial ASTs do not close all variants. |
| 2.10 Generalized Floating Point Interval Arithmetic | Finite endpoint candidate certification and conditional outward evaluation exist. | General family demotion/noncollapse and stored-bound evaluation correspondence, with 2.5/2.6/2.9 premises explicit. No new hardware rounding assumptions without approval. |
| 2.11 Interval Function Domains (1–5) | Universal compatibility, exact input-domain envelopes and partial guards exist; finite conjunction/classification bridge now local. | Numeric domain descriptions and classification-preserving demotion must connect to same-input inclusion/extension, including empty fibers and undefined values. The new predicate-level family theorem is not the full numeric language. Verify simplicity examples with exact source wording. |
| 2.12 Property Tracking | Restricted semantic continuity and source counterexamples exist. | Resolve the documented implication/continuity-specialization tension, specify weak/strong recursion faithfully, and prove only statements supported by the resulting explicit interpretation. Structural certificates are not automatically semantic equivalences. |
| 2.13 Interval Sets | Finite covers and restricted split reciprocal images exist. | General set inclusion/extension, demotion, preservation of domain information, and source bumpy-function claims; distinguish exact image from covering union. |
| 2.14 Variants | Selected equal-bound/uncertain-coefficient instances. | Source-checked mathematical correspondence for claimed mixed/equal-bound variants; do not count a single specialization as the whole section. |
| 2.15 Real Representations (1–8) | Library real foundation; survey mapping unfinished. | Inventory all eight subsections (not just the first three in the transcription), map relevant mathematical claims/dependencies, and distinguish surveyed representations from required runtime implementations. |

## Critical path, in dependency order

1. **A — Domain classification and shared constraints (current local slice).**
   Depends on #32's finite Boolean operations and existing universal-domain
   contracts. Prove same-parameter conjunction, pointwise classification weakening,
   and actual-semantic bridges. Keep #32 first in review order; no merge assumed.
2. **B — Finite logical/domain interface closure.** Complete the source's
   optimistic/pessimistic projections and remaining finite comparison relations;
   connect the Boolean membership reading to numeric domain-description examples.
   Source-check each `f_i` and its demotion obligations rather than assume all
   ordinary numeric roundings preserve arbitrary classification functions.
3. **C — Extended/exceptional semantic foundation.** Audit 2.5–2.6 and the λ
   conventions needed by 2.8/2.11. Establish the mathematical model and explicit
   correspondence before extending hull/demotion statements to infinities/empty
   images. This is a semantic-design checkpoint, not a native implementation task.
4. **D — General family inclusion and demotion.** With C fixed, unify the
   existing finite instances under the source's 2.9 family semantics and close
   2.10's model-level demotion/noncollapse claims. Review parameter dimension,
   domain restrictions and actual shared witnesses explicitly.
5. **E — Full domain extension and property tracking.** Complete 2.11 against
   C/D; then address 2.12's source tension. A corrected or narrower statement must
   be labeled as such and accepted explicitly before it can count toward closure.
6. **F — Sets, variants and final source audit.** Close proof-bearing 2.13/2.14
   gaps using C/D/E, finish the 2.1–2.4/2.15 library/survey mappings, and run an
   end-to-end source/theorem/assumption audit of every checklist row.

Foundational mappings and source analysis can proceed while proof PRs await
review; do not create unnecessary dependencies on unmerged implementation work.
Each publication remains a bounded reviewed milestone. Oldest-ready PR first,
subject to explicit dependencies; broad ownership does not authorize merges.

## Decisions to surface, not silently make

* A source-faithful extended-real/undefined model may differ from an existing
  library's conventions. The tradeoff must be documented before a broad migration.
* The known 2.12 continuity-specialization counterexample prevents simply calling
  the printed implication a proved general continuity theorem. Authorial intent
  is not known; keep the counterexample and proposed interpretation separate.
* A stronger FP model or hardware assumption requires John. Mathematical
  conditional theorems and proven finite decoding do not grant that permission.

These do not block A/B or the library/source mappings. They do prevent an honest
claim that finishing a few more finite APIs alone completes Chapter 2.

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

## Exact partial-operation transfer

[Partial image transfer](PARTIAL_IMAGE_TRANSFER.md) proves a common exactness
criterion for injective partial real graphs and a checked finite-gap certificate,
instantiated by square root and guarded reciprocal. Exact output images preserve
possible definedness, not universal input-domain classification. This advances
the derived §§2.7/2.11 conversion bridge without claiming the full constructive
numeric/domain-description demotion or adding exceptional arithmetic rows.

## Constructive finite value/domain conversion

[Piece-domain conversion](PIECE_DOMAIN_CONVERSION.md) constructs a closed value
enclosure and explicit feasibility code for the existing guarded mixed bands,
preserving each choice's definedness and the family's definite/possible flags.
It does not claim numerical image equality or arbitrary descriptor synthesis.
The [current closeout matrix](CHAPTER2_CLOSEOUT.md) consolidates covered results,
remaining proof gaps, source inconsistencies under stated readings, and
unspecified semantics; it supersedes older residual lists where later proofs
have closed an item. Chapter 2 remains incomplete.

## Guarded composition with generated domains

[Guarded piece composition](GUARDED_PIECE_COMPOSITION.md) connects generated
finite-band descriptors to the existing expression evaluator, with exact domain
classification and sound values on checked success at one parameter and choice.
Failed whole-hull guards remain unknown. The [closeout matrix](CHAPTER2_CLOSEOUT.md)
now distinguishes this covered bridge from missing operation-generated splitting
and output representation for inconclusive guards. No exceptional rows or FP
premises change.
