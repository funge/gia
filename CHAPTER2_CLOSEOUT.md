# Chapter 2 closeout matrix

The current [subsection-by-subsection audit](CHAPTER2_CHECKLIST.md) was checked
against printed pp.13–43, including the formulas rather than only transcription.
It is the authoritative source-to-Lean map; older receipts in the
[source audit](CHAPTER2_SOURCE_AUDIT.md) remain historical evidence.

| Classification | Current position |
| --- | --- |
| Imported foundations | Integer, rational, real, complex and positive-infinitesimal constructions use pinned mathlib with explicit correspondence theorems. |
| Core mathematical coverage | Actual-image least hulls, same-witness inclusion and demotion, finite exact comparisons/Boolean composition, strict domain factorization, guarded value/domain conversion, finite family/set representations, and supported stream arithmetic/search are proved. Generic relational theorems do not synthesize arbitrary converters. |
| Concrete representation coverage | Finite formats and their repaired binary64 correspondence, finite affine/quadratic/Hansen variants, unbounded sets of finite choices, cuts, rational sequences, radix digits with explicit floating normalization, and simple/signed continued fractions have scoped proofs. |
| Checked source obstructions | Literal coefficient/digit format disagreement; literal decimal rounding/reassociation discrepancies; pointwise forward-or-reverse affine claim; semantic weak-continuity implication; unconditional staged floating-interval subdistributivity. Each has a checked control and a separate valid scope or repair. |
| Unresolved source interpretation | Full exceptional arithmetic/carrier promotion, weak-tracking meaning, and compatible operation/demotion choices in claimed homomorphisms. Missing rows are not filled from IEEE. |
| Concrete proof correspondence still missing | The displayed symbolic sin/root trace. Concrete constant add/sub/mul and linear-evaluator compatibility are already proved; only a generalization to arbitrary demotion choices would require new compatibility premises. |
| Restricted later operator coverage | Interval-stream convergence covers the existing strict finite arithmetic grammar; operators introduced later need their own correspondence proofs. |
| Not new universal Chapter 2 obligations | General nonlinear quantifier elimination, automatic bumpy classification, arbitrary optimal demoters, unspecified online circuits/interval Euclidean extraction, and uniform performance claims. These are definitions, references or optional implementations rather than supplied universal algorithms. |

## What changed in this closeout

[FloatingDigits](FloatingDigits.lean) closes all-real sign/scale/digit coverage
for every radix at least two. Uniqueness is proved with canonical fractional
digits and the explicitly chosen half-open normalization [1/b,1); the source's
zero-tail condition alone does not fix scale. Zero is handled separately.

[RoundedIntervalControl](RoundedIntervalControl.lean) proves that exact rational
interval subdistributivity does not survive arbitrary staged least outward
rounding: in the existing literal decimal format, I=[2,2], J=[100,100], K=[1,1]
give left enclosure [200,220] and right enclosure [200,210]. Every rounding stage
is certified least, and the true answer 202 is enclosed on both routes.
This does not change any arithmetic backend or trusted premise.

## Finish-line recommendation

Stop growing the chapter through optional nonlinear or representation algorithms.
Close the concrete symbolic correspondence above, then explicitly decide how
errata and unspecified source semantics are recorded. The most consequential
blocker to claiming every printed statement is proved is **source interpretation,
not a missing solver**. Do not introduce an axiom to settle it.

A defensible current description is: “Chapter 2 has a complete subsection audit
and a formalized core at explicitly stated scopes, with imported foundations,
restricted counterparts, checked counterexamples and unspecified claims
catalogued.” This is not an unconditional declaration that Chapter 2 is complete.
