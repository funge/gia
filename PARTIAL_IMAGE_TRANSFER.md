# Exact image transfer through partial operations

This is a derived mathematical bridge for Tupper's inclusion and domain framework, not a new exceptional arithmetic table. The source distinguishes value inclusion from domain classification in §2.11.1–2, printed p.34 / [PDF p.50](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=50) (visually checked), building on §§2.7.3–4, printed pp.24–25 / [PDF p.40](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=40). The existing [root interpretation](ROOT_TRANSFER.md) and guarded reciprocal are reused. The reciprocal relation is the existing `GeneralizedExamples.ReciprocalValue`; its zero guard is not mathlib's totalized inverse at zero.

## Common exactness rule

[PartialImageTransfer.lean](PartialImageTransfer.lean) reuses `GeneralFamilyDemotion.outputs` for the actual relational image. Let `S ⊆ T`, let `D(x)` mean that the partial graph has some output at `x`, and assume the graph is injective: two inputs with the same output are equal. Then:

```
image R T = image R S  ↔  ∀ x ∈ T, D(x) → x ∈ S
                      ↔  T ∩ D = S ∩ D.
```

The sufficient direction does not require injectivity, functionality or totality. The converse needs injectivity; a checked constant-operation example refutes it otherwise. `image_mono` preserves every original value using its original input witness. These statements can be applied separately at each fixed parameter and external witness, by specializing `R`, `S`, and `T`; they do not justify projecting away a correlated witness. Input membership is not evidence that every enclosed input was originally attainable.

For square root, injectivity and the domain `x ≥ 0` are proved, with a definitional bridge to `RootTransfer.roots`/`SqrtValues`. For reciprocal, injectivity and the domain `x ≠ 0` are proved from the existing guarded relation. `reciprocal_remove_zero` proves exact image equality for arbitrary sets after removing zero. Empty, unbounded and disconnected finite-real sets are allowed; no literal infinity or λ is a value in this theorem.

## Executable finite-gap certificate

`exact_of_finite_gaps` requires a proof that every added input belongs to a supplied finite list of labeled points. `blocked?` decides that none of those labels denotes a point in the operation domain. The label-domain interpretation is another proof obligation. The fixtures use exact rational labels and decidable rational comparisons; real geometry is **not** decided by this checker.

This is a sufficient certificate, not a complete automatic algorithm: the list may overapproximate the gaps, and rejection is inconclusive. An infinite gap cannot in general be handled by this finite-point certificate. There is no hardware caller, no rational arithmetic inserted into a hot path, and no new floating-point assumption.

[Kernel fixtures](tests/PartialImageTransfer.lean) exercise the checker through the transfer theorem:

- Closing the negative endpoint of `(-1,4]` preserves the root image.
- Closing the zero hole of `[-1,1] \ {0}` preserves the reciprocal image; `{0}` alone has no reciprocal value.
- Adding zero to `[-1,0)` creates a root, so equality fails.
- Omitting reciprocal input 1 loses output 1, whether the hole is a boundary or interior point.
- A mixed finite gap list containing 0 and 1 is rejected for reciprocal.
- Empty images and the failure of necessity without injectivity are checked.

`possible_iff` preserves existence of a defined input when images agree. It does **not** preserve universal definedness: adding zero to the reciprocal input `{1}` changes an all-defined set into a mixed set without adding an output. The fixture `totality_not_preserved` checks this distinction. Therefore this milestone is not a complete classification-preserving domain-description demotion, nor does it replace the existing `DomainBounds` obligations.

## Remaining Chapter 2 work

The most consequential missing formalization is a constructive, source-scoped conversion that computes both numeric and domain descriptions for a reusable family class and proves the §2.11.2 classification obligations together. The present finite-gap certificate discharges exact-image premises in a useful restricted case, but neither discovers the gaps nor synthesizes such domain descriptions. Existing general preservation interfaces and leaf conversions do not constitute a complete implementation of that source construction.

Separate source issues remain: the literal coefficient/digit format discrepancy and the weak-property-tracking interpretation are documented counterexamples/qualifications; unspecified exceptional arithmetic rows cannot be completed by guessing. These are distinct from the missing constructive proof above. Chapter 2 is not declared complete.

Run `./check.sh`; exact-candidate evidence is recorded in [VALIDATION.md](VALIDATION.md). No native/default changes, performance claims, new axioms or expanded FP contracts.
