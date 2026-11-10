# Floating-point target: Tupper first

The goal is proved interval arithmetic executing with hardware floating point.
The subsequent [hardware addition milestone](HARDWARE_ADDITION.md) demonstrates
native execution under an explicit adapter contract; it does not close the
representation or runtime-refinement gaps listed below.
[Restricted-domain hardware sine](HARDWARE_SINE.md) now implements the §3.1.6
Taylor construction on [0, 1], under those primitive contracts, with a proved
analytic remainder. It does not supply a correctly rounded transcendental operation.
See the [hardware architecture assessment](HARDWARE_FLOAT_PLAN.md), prepared after
John clarified this goal; its decision points supersede the next-step suggestions
below. Exact rational execution is supporting groundwork, not the runtime target.

The initial source target is the floating-point system, rounding contracts and generalized
interval treatment in Tupper's thesis, alongside the [C operation ledger](OPERATION_COVERAGE.md).
This is a gap map, not a claim that the existing rational proofs formalize a machine
format. Verification of C execution and its IEEE 754 refinement remains a separate
later layer. No new floating-point assumption is introduced here.

## Source and comparison

Earlier source checking used a graphing technique inventory (historical private project record; not bundled)
and source review (historical private project record; not bundled),
covering directed rounding and two-stage demotion. Use the public original citations
in the concordance; neither private record is a prerequisite. The following comparison
was checked visually against the repository thesis PDF, printed pp. 19–20 and
32–33 (PDF pp. 35–36 and 48–49). Markdown is only a transcription aid. Other
source leads in the [concordance](THESIS_CONCORDANCE.md) remain separately qualified.

| Source obligation | Existing Lean result | Remaining gap |
| --- | --- | --- |
| [§2.5, p. 19](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=35): finite significand/exponent system; exact storage format deliberately left unspecified | `QInterval` represents finite rational endpoints interpreted over reals | No representable-number set, exponent/precision model, normalization or subnormal correspondence |
| [§§2.5.1–2.5.2, p. 19](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=35): infinities and invalid result λ | Partial `Value` semantics and explicit domain certificates handle mathematical undefinedness | These are not floating-point NaNs or infinities. No exceptional-value encoding or comparison model |
| [§2.5.3, p. 20](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=36): upward/downward rounding brackets the exact value; approximate function bounds may be loose | [RoundedAddition](RoundedAddition.lean) proves addition enclosure under explicit outward inequalities. [EvaluatorRounding](EvaluatorRounding.lean) proves evaluator soundness when successful optional rounding results satisfy those inequalities | No concrete rounding algorithm, nearest-result property, representability, ULP error or transcendental implementation guarantee |
| [§2.10, p. 32](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=48): bound-description functions with machine coefficients, noncollapse at every parameter | [LinearIntervals](LinearIntervals.lean) supplies exact rational affine coefficients and pointwise bounds; [PartialEnclosures](PartialEnclosures.lean) supplies domain-aware semantic bounds | No machine-coefficient family or coefficient-conversion algorithm |
| [§2.10, p. 33](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=49): inclusion quantifies over a common parameter and represented inputs | Existing shared-parameter and shared-environment interpreters preserve these witnesses; see the concordance | Their exact rational arithmetic is not the thesis's floating-point generalized extension |
| §2.10, p. 33: two-stage conversion from ideal bounds through a chosen real family to machine coefficients | Exact-family enclosure proofs provide part of the first stage | No verified second-stage coefficient demotion. The source's machine-precision comparison is not a proved error bound here |
| §2.10, p. 33: outward evaluation of bound functions at a parameter | Existing directed backend handles ordinary finite interval bounds | No generalized bound-function evaluator with certified outward results at a shared parameter |

An important source distinction needs a deliberate specification before extension:
p. 19 treats equal signed infinities as incomparable and even prints infinity
self-equality as false. This is not Lean equality or its usual extended-real order.
A faithful account must distinguish the source's comparison relation from equality;
we must not silently import that relation as an IEEE or standard order model.
This document records the issue, without choosing a new model or adding axioms.

## Compatible next steps and decision boundary

The [monotone endpoint milestone](MONOTONE_INTEGER_BOUNDS.md) supplies a reusable
finite, attained-endpoint prerequisite from §§3.2.10–3.2.13. Its endpoint bounds
may already be loose. It therefore composes mathematically with certified outward
bounds without assuming a format or a particular rounding implementation. Floor
and ceiling now have exact rational implementations, enclosure and least-interval
proofs; their C implementation is still unverified.

The next narrowly scoped §2.10 bridge should reuse existing domain-aware enclosure
contracts to prove that pointwise outward widening preserves enclosure on the
same domain and at the same input witness. Before adding an API, check whether
existing weakening lemmas already express it. This concerns bound evaluation,
not coefficient conversion: rounding each coefficient separately is not a valid
argument for an arbitrary bound-function family. Neither widening nor a failed
range calculation may establish definedness, continuity or absence.

A subsequent finite affine coefficient-demotion construction could establish its
outward inequalities from a concrete error budget. It should be specified and
checked before implementation; the present roadmap does not assume that such a
budget exists. Adding an extended-value model, changing overflow behavior, adopting
new error/ULP contracts, or claiming a specific IEEE format needs review with John.
The already approved conditional downward/upward enclosure assumptions remain the
only floating-point contracts used by the current proofs.

For C correspondence, follow the per-operation pinned implementation links in
[OPERATION_COVERAGE.md](OPERATION_COVERAGE.md). That layer must eventually account
for finite and exceptional values, libm/fenv behavior and representation. None of
those implementation properties follows from the abstract real enclosure theorem.
