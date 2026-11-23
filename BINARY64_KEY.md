# Binary64 key foundation — local proof checkpoint

[Binary64Key.lean](Binary64Key.lean) starts the requested inexpensive selector
correspondence. It is a **foundation checkpoint, not a qualified replacement
selector**. The exact [Word reference](WORD_TWO_CORNER.md) remains unchanged.
There is no native integration or benchmark in this change.

For `S = 2^63`, magnitude is `m = w % S`. The finite guard is
`w < 2^64 ∧ m < 0x7ff0000000000000`. The comparison key is `S + m` on the
nonnegative half and `S - m` on the negative half. Both signed zeros have key S.
These are comparison keys; they are never substituted for original operand bits.

## Kernel-checked results

- `exponent_magnitude` relates the existing decoder's exponent to magnitude.
- `finite_iff` proves the inexpensive Nat guard succeeds exactly when the existing
  optional rational `Binary64.decode` succeeds, including oversized raw input.
- `key_fits` proves finite keys fit in 64 bits; `key_zero` proves the zero tie.
- `magnitude64`, `finite64`, and `key64` are concrete UInt64 operations (unsigned
  remainder, comparison, addition/subtraction). `magnitude64_eq`, `finite64_eq`
  and `key64_eq` connect them to the Nat specification. The key proof rules out
  wraparound; it does not assume machine arithmetic is exact without proof.
- `key64_le`, `key64_lt`, `key64_equal` transport comparison/equality to the Nat
  keys. They **do not yet relate key order to decoded rational order**.
- `checkedKey` rejects oversized Nat words before UInt64 conversion.
  `checkedKey_spec` proves exact optional key agreement and
  `checkedKey_available` characterizes successful decoding. This function
  returns a key, not a quotient request or an enclosure.
- `nonnegative_order` and `negative_order` prove raw-magnitude ordering and
  reversal on their respective halves, again not yet decoded rational order.
- `units e f` is `f` when `e=0` and `(2^52+f)*2^(e-1)` otherwise.
  `units_upper`, `units_lower`, `units_strict`, and `magnitude_units_strict`
  establish strictly increasing unsigned magnitude in minimum-subnormal units,
  including binade transitions. These integer-unit definitions are not executed
  in the proposed UInt64 key hot path.

The tests check finite extrema, subnormals, the normal boundary, adjacent binades,
negative order reversal, signed-zero equality, infinity, quiet/signaling NaN bit
words, oversized Nat rejection and the concrete UInt64 bridge. They use kernel
proofs, not `native_decide`. Existing WordTwoCorner no-call/six-row/failure fixtures
remain in the full gate; no unproved new request dispatcher is introduced.
Additional reference controls assert the actual ordered raw request pairs for
`[-0,1]/[2,4]`, `[-0,-0]/[2,4]` (nonnegative-first priority), and `[+0,-0]/[2,4]`.
They also prove no calls for oversized numerator words (`2^64` and `2^64+1.0`'s
raw word) and reversed subnormal `[0x2,0x1]` bounds. They do not substitute equal
quotient bits for equal requests or use host DAZ comparisons.

## Work still required before selector qualification or timing

1. Prove the existing rational decoder equals the signed integer-unit value
   divided by `2^1074`. This must cover both decoder power branches and sign.
2. Compose that identity with integer-unit strict ordering and signed-zero cases
   to prove key order/equality iff decoded rational order/equality for finite
   words. UInt64-to-Nat comparison transport is already available here.
3. Define the key-based four-endpoint guard and six-row dispatcher retaining the
   original raw operands. Prove exact `Option Requests` equality with
   `WordTwoCorner.requests` on **all** Nat inputs, before transporting standalone
   enclosure, no-call and conditional refinement theorems.
4. Only then qualify and time the actual proved route: selector-only and compiled
   end-to-end comparisons against rational-reference and four-corner paths,
   including invalid/zero/subnormal/overflow/caller-state controls.

No equality of two independently sound arithmetic implementations follows from
key correspondence. Omitted-call failure, paired-bound availability, signed-zero
raw output differences and caller FP status remain separate obligations.

The native Float/Word bridge is still outside the proof. The prior experiment's
NaN canonicalization and unqualified signaling-NaN transport caveat remain; raw
Word fixtures here are not tests of native Float transport. No C/FFI files,
default runtime path, FP assumptions or Chapter 2 work are changed.

## Context and checks

This is an implementation-refinement prerequisite for the finite binary64
interpretation documented in [BINARY64.md](BINARY64.md), not a new Tupper theorem,
a complete IEEE 754 verification, or an optimized quotient deployment. Tupper's
outward finite arithmetic remains the surrounding application; the existing
[division proof](TWO_CORNER_DIVISION.md) and [refinement](TWO_CORNER_REFINEMENT.md)
provide the theorem targets to reuse after request equivalence is proved.

Run `lake build Binary64Key`, `lake env lean tests/Binary64Key.lean`, and
`./check.sh` with the pinned project toolchain. Audit registration includes all
new named theorems and namespace-wide enforcement. Qualification details are
recorded in [VALIDATION.md](VALIDATION.md).
