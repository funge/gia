# Certified pi and finite whole-period sine reduction

This extends the [signed hardware sine kernel](HARDWARE_SINE.md) with a bounded
argument-reduction search. It uses hardware binary64 multiplication and
subtraction, then the existing proved kernel on [-1, 1]. It does not call libm
sine, floor, remainder, fractional part or an integer-conversion routine.

## Source and deliberate scope

Tupper §3.1.5, printed pp.47–48
([original PDF page 63](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=63)),
uses sin(x + 2πn) = sin(x) and interval arithmetic to bound the reduced argument.
The original PDF pages were visually checked. The repository Markdown transcription
incorrectly shows a quarter in places where the original reduction formula uses
one half; the PDF is authoritative. The existing Taylor kernel follows §3.1.6.

The present algorithm is a restricted implementation of the periodicity/interval
principle, not a transcription of the source's fractional-part algorithm:

1. Try n = 0, 1, -1, 2, -2, in that order.
2. Form an enclosure of 2nπ using the certified pi interval and directed multiply.
3. Subtract that entire enclosure from the input interval using directed subtract.
4. Invoke the signed kernel only if the whole residual interval fits in [-1, 1].
5. Return the first successful enclosure; return unknown after all failures.

This supports intervals near 0, ±2π and ±4π. It is **not** complete even on the
span between them: 1.5 is deliberately unknown, as are intervals crossing too
much of a period, inputs outside the finite search, and exceptional values.
Even an exact residual touching ±1 can be rejected when pi/rounding uncertainty
widens it past that boundary. No narrower domain guarantee is silently assumed.
Covering neighborhoods of extrema needs a cosine kernel or a wider proved local
method; large-argument reduction and automatic integer selection remain future
work. None of these gaps is treated as mathematical undefinedness.

## Proved constants and reduction

[PiBounds.lean](PiBounds.lean) defines exact real dyadic bounds

```
L = 7074237752028440 / 2251799813685248
U = 7074237752028441 / 2251799813685248
L < π < U,       U - L = 2^-51.
```

The proof derives these inequalities from mathlib's kernel-checked
[twenty-decimal pi bounds](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/Data/Real/Pi/Bounds.lean). It does not assume a decimal oracle or use native evaluation in a proof.
They correspond to binary64 bit patterns `0x400921fb54442d18` and
`0x400921fb54442d19`. Their finite decoding remains part of the existing adapter
boundary; `decoded_contains` combines those exact-value premises with the proved
real inequalities. The pi-containment claim itself is not an adapter assumption.
The regression `lower_singleton_misses` proves why treating the lower approximation
as exact pi is invalid.

[SineReductionProgram.lean](SineReductionProgram.lean) supplies the shared monadic
program, instantiated with IO for native execution and Id for proofs.
[SineReduction.lean](SineReduction.lean) proves:

- `reduce_encloses`: any certified integer-period shift preserves the sine value
  and encloses every input point on successful evaluation.
- `searchPeriods_encloses`: any finite list of certified candidates preserves
  that property, including retries after failure.
- `periodCandidates_sound`: the actual five-candidate list has the required
  integer witnesses under existing constant-decoding obligations.
- `signed_kernel_sound`: the kernel obligation follows from the previous signed
  endpoint proof, which in turn follows from the proved Taylor program and
  primitive operation contracts. No separate sine-accuracy assumption is added.

All points in an interval use the same selected integer for a successful attempt.
The existing `SinValues` lifting preserves arbitrary external domain relations
and input witnesses. Successful numeric evaluation does not fill an external hole
or establish the existence of an admissible input.

## Trust and numerical limits

There is no new floating-point contract. The code instantiates the existing finite
constant-decoding obligations with the two explicit dyadics and coefficients
0, ±2, ±4. Finite comparisons, directed arithmetic and IO/FFI/compiler/hardware
refinement remain trusted as before. The native FFI adapter is unchanged. The
formal results do not prove Float bit decoding or the compiled implementation.

Uncertainty from the pi enclosure is propagated, never discarded. Before operation
rounding, a fixed shift 2n[L,U] has width |2n|·2^-51. Subtraction and kernel arithmetic
add rounding and approximation error; the 1/5040 point Taylor budget is not a
bound on the final output width. This is not correctly rounded sine. We do not
claim full-range or high-precision argument reduction.

The initial C comparison target remains relgraph's
[`gi_trans_sin`](https://github.com/funge/relgraph/blob/7fd4b39dc127dec3be1b96a46cf392d4bcd73d2b/src/transcendental.c#L645)
and [public API](https://github.com/funge/relgraph/blob/7fd4b39dc127dec3be1b96a46cf392d4bcd73d2b/include/graphing/transcendental.h).
Those implementation links may require access; GIA builds independently. That
implementation uses MPFR and periodic extrema handling. No correspondence to it
is proved here, and no relgraph library code is changed or copied.

## Verification

Run `./check.sh` and `./hardware/check.sh` with the pinned toolchain. The native
suite retains all prior tests, adds 92 supported reduction vectors, and checks
exceptional inputs, exhaustion and injected primitive failure. The independent
[reduction oracle](hardware/check_reduction.py) verifies the pi constants against
rational Machin-formula bounds, simulates each directed operation exactly, and
checks nine samples per interval with a higher-degree sine series at the original
input. The latter does not depend on pi or the runtime reduction formula.
Rational arithmetic is used only in this test oracle, not in the runtime.

The [Lean fixture](tests/SineReduction.lean) separately checks composition with
an exact-real client, retry/exhaustion/failure behavior, external holes and the
counterexample to an exact singleton pi approximation. These tests and local
source review do not replace independent human review or implementation proof.
See [VALIDATION.md](VALIDATION.md) for the qualification receipt.
