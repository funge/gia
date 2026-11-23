# Proved UInt64-key two-corner selector

[KeyTwoCorner.lean](KeyTwoCorner.lean) supplies an executable selector whose
**ordered raw requests, including rejection, equal the exact rational reference
on every raw Nat input**. Keys are UInt64 values; original operand words are
retained unchanged. The prior [foundation checkpoint](BINARY64_KEY.md) and
[Word reference](WORD_TWO_CORNER.md) remain independent history.

## Proof chain

`Binary64Key.decode_scaled` proves, for every accepted rational `q`,
`q * (2:ℚ)^1074 = sign(w) * units(exponent(w), fraction(w))`.
It handles subnormals and both normal power branches of the unchanged decoder.
`decode_signed` rewrites that in terms of unsigned magnitude units and sign.
`key_signed_le` combines unsigned binade strictness, sign reversal and both zeros.
`decoded_key_le`, `decoded_key_lt` and `decoded_key_eq` then establish the exact
order/equality correspondence for decoded finite words. No rational calculation
is needed in the executable key path; this is the proof-side interpretation.

The foundation's `key64_eq` and comparison lemmas connect concrete UInt64
arithmetic to Nat keys without wraparound. `checkedKey` rejects oversized Nat
inputs **before** conversion and rejects all nonfinite words. The selector
validates all four words, checks both interval orders and strict separation of
the denominator from zero, then uses the same six rows and nonnegative-first
zero priority as the reference.

The central statements are:

```lean
requests_eq (I J : Bounds Nat) :
  requests I J = WordTwoCorner.requests I J

run_eq (call) (I J : Bounds Nat) :
  run call I J = WordTwoCorner.run call I J
```

`run` has an explicit dispatch trace. `rejected_no_calls` proves rejection reaches
no callback; first-call failure skips the second. `run_eq` compares the same
pure call denotation, including its `none` outcomes. It is not a theorem about
independently conformant hardware executors, hidden effects or FP status.

`run_sound` transports standalone quotient enclosure and `y ≠ 0` using only the
two selected `CallSound` obligations and successful assembly. Old four-corner
success is **not** a premise. Separately, `run_refines` preserves the old-success,
selection soundness and matching retained decoded Down/Up observations needed
for one-way containment. Neither result asserts raw-output equality, equal
availability, or harmlessness of omitting failing calls.

## Controls and execution boundary

Kernel fixtures test all six rows, exact ordered signed-zero requests, oversized
inputs, reversed subnormals and first-call failure traces. Existing reference
fixtures and the foundation's binade/extreme/nonfinite controls stay in the full
gate. No `native_decide`, new axiom or FP assumption is used.

The opt-in [native experiment](experiments/key_two_corner/README.md) compares the
actual proved `requests` against the rational reference and unchanged four-corner
baseline. Its Word API includes Nat range checks, UInt64 conversion and keys;
those costs are included, not replaced by an unproved Float sign dispatcher.
Native Float transport, Lean code generation, adapter/compiler/hardware and
caller-environment behavior remain the existing empirical/trusted boundary.
NaN payload/signaling canonicalization is recorded separately. No native library,
C arithmetic, default target/path or renderer integration is changed.

This is a verified implementation refinement of the existing finite guarded
quotient rule, not a new Tupper result, exact-rounding theorem, global availability
equivalence, or proof of C execution. The mathematical division scope and source
correspondence remain in [the two-corner proof](TWO_CORNER_DIVISION.md).
