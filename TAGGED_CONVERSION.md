# Tag-preserving family conversion

This is a derived mathematical representation theorem, not a transcription of
an exceptional arithmetic table. Tupper §2.5.2 (printed p.19 /
[PDF p.35](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=35)) distinguishes
lambda/undefinedness; §2.6 (printed p.21 / PDF p.37) displays the real carrier
with two signed infinities, without lambda. Both original page images were
rechecked. §§2.9.1 and 2.11 motivate family inclusion and separate domain
classification. The conversion below states exactly the supported common set
interpretation; it does not resolve the full F→R* homomorphism claim.

## One conversion interface

[TaggedConversion.lean](TaggedConversion.lean) reuses the existing
`ExceptionalComparisons.Value` carrier. A family S is a set of finite real
payloads, literal negative/positive infinity tags and a distinct lambda tag.
`finitePart S` extracts only the real payloads. `lift C S` applies the supplied
real-set converter C to that part and retains membership of EACH exceptional
tag exactly. Infinite bounds inside C do not create literal infinite values.

This is a proof-side semantic conversion, not a finite encoding or an arithmetic
operation on these tags. Lambda is deliberately retained in the family as an
undefined alternative, not treated as an attainable real output. Source numerical
comparison, Lean equality and the structural category observation remain distinct.

`lift_comp` proves exact denotation:

```
lift D (lift C S) = lift (D ∘ C) S.
```

It needs no inclusion or rounding assumption. It does not say C or D is exact:
lossy real hulls still obey this conversion-composition equation.

`composition_preserves` assumes only that C and D each contain their real input
sets and preserve the empty set. It proves the equation at every shared parameter,
source-to-result membership inclusion, and domain-classification refinement for
ANY predicate on the existing tags. It reuses
`DescriptorDemotion.widen_refines_iff`; there is no duplicate domain interpreter.
`guarded_witness` reuses `witness_compatible` with the same original tag and an
external domain predicate A. It proves compatibility with `A ∧ P v`; a missing
input cannot be replaced with a value selected from a widened family.

## Stronger exact definedness result

For P(v) meaning v≠lambda, `defined_exists` and `definedness_exact` prove exact
possible AND definite bits under those premises. Finite widening preserves whether
there is any finite alternative; both infinities are non-lambda tags; lambda's
membership is unchanged. The existing nonempty guard on definite classification
is retained for empty families. This is definedness of the represented alternatives,
not totality of an unspecified operation applied to them.

The concrete chain uses the already-proved `ExtendedImageHull.hull`, followed by
`NumberPromotion.hull`. Inclusion/empty premises are discharged by their existing
theorems. `hull_chain` proves arbitrary-predicate refinement; `chain_defined_bits`
in the fixtures proves exact definedness through the actual two-stage chain.
Thus this is more than a conditional interface with an uninstantiated converter.

## Checked controls

[Fixtures](tests/TaggedConversion.lean) cover all four categories, exact chain
composition, both exact definedness bits, the empty family, and an external hole.
The family of all real payloads does not acquire either literal infinity or lambda,
even when its numerical hull uses infinite endpoint bounds.

`finiteOnly` and `restoreFinite` model the tempting Option Real shortcut.
Kernel `decide` proves that both signed infinities collapse to lambda, whereas a
finite payload and lambda retain their respective categories. These are executable
structural functions and a decidable regression, not native Float/NaN transport.
A second control shows why empty preservation matters: C(S)=univ invents a defined
finite alternative from a lambda-only family. Arbitrary-predicate refinement does
not imply equality of classifications; exactness is proved separately for definedness.

## Review placement and limits

This milestone follows the integrated Chapter 2 units and reuses
[descriptor demotion](DESCRIPTOR_DEMOTION.md), the exceptional carrier and
real/integer hulls. It introduces no dependency on the property/accuracy proofs.
The source and fixtures are preserved from the qualified research checkpoint;
rehearsal notes, recovery bundles and historical integration material are excluded.

This closes exact composition and definedness preservation for an explicit tagged
set conversion. It does not construct every source number family, assign omitted
exceptional operations, prove preservation of rounded arithmetic or the source
numerical comparison table, provide a finite representation algorithm, or verify
IEEE/native execution. No new FP assumptions, C/FFI/default changes are involved. Chapter 2 is not complete.
