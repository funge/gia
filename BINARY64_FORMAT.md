# Repaired finite format and binary64 denotation

[Binary64Format.lean](Binary64Format.lean) proves the full equivalence

```
Repaired format q ↔ ∃ w, Binary64.decode w = some q
```

where `format = (radix=2, precision=53, minimum=-1022, maximum=1023)`.
This is equality of **finite rational value sets**, including normal and
subnormal values, both signs and zero. It is not equality of encodings, a native
execution theorem, or a statement about rounding exceptional values.

## Source and model boundary

Tupper §2.5, printed pp.18–19 /
[PDF pp.34–35](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=34), supplies
the two format displays and a binary64 parameter example. As proved and explained
in [the coefficient/digit comparison](FORMAT_DIGITS.md), those displays cannot
be identified literally. This milestone uses **only the explicitly repaired**
external-sign / `A` magnitude-digit family. It leaves `FiniteFormat.values` and
the printed strict `b^(A−1)` coefficient model unchanged.

The target is the existing pure Lean [Binary64.decode](Binary64.lean), which
extracts sign, exponent and fraction and rejects nonfinite or oversized raw
words. Its decoder semantics are the target definition, not a newly assumed
hardware contract. Nothing here promotes the source's prose description of bits
into an IEEE implementation proof.

## Proof chain

* `decode_formula` expresses every successful decode using the repaired digit
  evaluation. Exponent field zero uses fraction alone at exponent −1022;
  nonzero exponent fields use `2^52 + fraction` at `field − 1023`.
* `decode_presentation` proves these are admitted normal-or-minimum presentations.
  `subnormal_presentation` and `normal_presentation` expose the two cases.
* `pack_fields`, `pack_sign` and `pack_decode` prove finite raw-word construction
  from bounded exponent/fraction fields, preserving the chosen sign. These are
  natural-number bit encodings, not native Float conversions.
* `presentation_word` constructs a Word for every normal-or-minimum presentation.
* `double_shift` and `normalize_steps` preserve the rational value while doubling
  an under-normalized significand and lowering its exponent. Induction is bounded
  by the 2045-step exponent span; at the minimum it stops without discarding
  leading-zero, subnormal or zero values. `normalize` covers every admitted
  repaired presentation, including those not initially normalized.
* `repaired_iff_decode` composes both directions. `repaired_iff_binaryValues`
  identifies this family with the existing finite mathematical demotion set;
  `repaired_fixed` reuses the existing directed-demotion theorem for its values.

The normal-or-minimum restriction now has the same projected value set as the
unrestricted repaired family for these parameters. This is a proved binary64
specialization, not a general-radix normalization claim. No uniqueness of
presentation is claimed: in particular the two signed-zero words decode to
one rational zero. Existential construction is not a production encoder API.

## Validation and limits

[Kernel fixtures](tests/Binary64Format.lean) cover both signed zeros, positive
and negative minimum subnormal, maximum subnormal/minimum normal, both extreme
finite values, explicit packing, an unnormalized converse input, and
infinity/quiet-NaN/signaling-NaN/oversized-word rejection. A mathematical demotion
client exercises the new correspondence without a native caller.

Run `./check.sh` with the pinned toolchain. The module and fixtures participate
in the existing axiom allowlist. No new project axiom, floating-point premise,
C/FFI change, runtime default, hardware test or benchmark is introduced. Native
Float bit transport, actual rounding-mode execution, NaN behavior, exceptions,
overflow handling and accuracy/performance guarantees remain outside this proof.
This closes the repaired finite binary64 denotation bridge, not the source's
literal-display equivalence or Chapter 2 as a whole.
