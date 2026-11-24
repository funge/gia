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

## Section-by-section exit criteria

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
