# Integer residues alongside real enclosures

[IntegerResidue.lean](IntegerResidue.lean) is a proof-first research
foundation. A real interval can be the least interval hull while losing enough
discrete information to prevent exclusion. The new propositions retain that
information without changing any AST, evaluator, renderer or runtime.

## Exact hypotheses and conclusion

`IntegerValue z` requires a witness `n : ℤ` with `z = (n : ℝ)`.
Floor and ceiling provide such witnesses. Exact integer scaling, addition and
subtraction preserve them. Integer **endpoints** of an enclosing interval do not.

`HasResidue d r z` means there exists `k : ℤ` such that
`z = ((r + d*k : ℤ) : ℝ)`. The residue need not be normalized. Addition,
subtraction and integer scaling propagate this certificate for the actual values.
`affine_residue` proves that integer provenance of `x`, together with checked
`d ∣ a` and `d ∣ b-r`, certifies `a*x+b` with residue `r` modulo `d`.
No finite-precision arithmetic is hidden in these exact algebraic statements.

For `0 < d`, `window_exclusion` proves:

```text
HasResidue d r z
floor((U-r)/d) < ceil((L-r)/d)
--------------------------------
not (L ≤ z and z ≤ U)
```

If a value lay inside that closed window, its integer witness would be at least
the ceiling and at most the floor, contradicting the strict inequality. The
strict test matters: a boundary lattice point must not be discarded. Zero and
negative moduli are outside this exclusion theorem; it never divides by zero.
Failure to meet the test provides no exclusion claim.

`relation_exclusion` applies at a single parameter `p` to actual values `R p z`.
`enclosure_window_exclusion` combines the same value's residue with an existing
`PartialEnclosure.Sound R`, applying the test to
`[max L (I.lower p), min U (I.upper p)]`. It does not choose independent input
witnesses, assert totality, or fill an external domain hole. The existing domain
contract and semantic relation are unchanged; the fixture permits any external
predicate, including the empty predicate.

## Checked examples and controls

The [semantic fixture](tests/IntegerResidue.lean) proves for `0 ≤ x ≤ 1`:

- `z = 2*floor(x)` is enclosed by `[0,2]`. Values 0 and 2 are attained, so every
  interval enclosing the image contains `[0,2]`: this is the exact interval hull.
- That hull overlaps `[1/2,3/2]` (at 1), yet parity excludes every actual value
  from the window: `ceil(1/4)=1 > 0=floor(3/4)`.
- The negative window `[-3/2,-1/2]` is also excluded, while the closed boundary
  value 2 is retained when the target ends at 2.
- Floor/ceiling affine divisibility, composite add/subtract and negative scaling
  certificates check. External-domain holes remain holes.
- At `x=0, y=1/2`, both inputs lie in the integer-endpoint interval `[0,1]`, but
  `2*floor(x)+2*y=1`. The fixture also proves `1/2` lacks integer provenance.
  Propagating parity through an arbitrary real term would therefore be unsound.

## Relation to existing work and limits

This is a derived discrete certificate, not a claimed transcription of a Tupper
result or a novelty claim. The existing [floor/ceiling milestone](MONOTONE_INTEGER_BOUNDS.md)
records thesis §§3.2.10–3.2.13 and its original-PDF review, proves attained endpoint
bounds, and already distinguishes least interval hull from discrete image.
The residue layer addresses that loss of information using integer arithmetic;
it does not claim to implement Tupper's branch labels or discrete-image machinery.
See the [source concordance](THESIS_CONCORDANCE.md) for those separate obligations.

No automatic provenance inference, modulus selection, runtime checker, hardware
floor/ceil refinement or C implementation equivalence is proved. No FP assumption
is added. These are ordinary mathematical Lean proofs; exact rational examples
are proof controls, not a replacement for the hardware runtime. There are no
speed, renderer or Bilevel applicability claims.

Run `lake build IntegerResidue`, `lake env lean tests/IntegerResidue.lean`, and
`./check.sh`. Named and namespace audits cover the library; the fixture has its
own namespace audit. See [validation receipts](VALIDATION.md). Independent semantic review found no blocking defects; the certificate layer
remains separate from runtime integration.
