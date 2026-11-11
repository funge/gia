# Certified split pi for larger sine arguments

This milestone represents pi as an exact dyadic high part plus a small interval
for the remaining real value. The native reducer keeps small corrections separate
until the large subtractions finish. It uses only the existing directed hardware
operations; no error-free-transform, exact-cancellation, FMA, integer-conversion,
or additional floating-point accuracy assumption is introduced.

## Certified constants

[SplitPi.lean](SplitPi.lean) uses the existing high value
`H = 7074237752028440 / 2^51` (bits `0x400921fb54442d18`) and proves

```
Tlo < pi - H < Thi
Tlo = 2483825185828341 / 2^104
Thi = 1242014004962189 / 2^103
0 < Thi - Tlo < 1.001e-20.
```

The tail bit patterns are `0x3ca1a60d3bc55bea` and `0x3ca1a66bae498e34`.
The real bounds follow from pinned mathlib's proved twenty-decimal bounds for pi.
They are not a numerical oracle or an extra adapter axiom. The split bracket is
more than 40,000 times narrower than the previous `2^-51` bracket; a Lean control
checks that comparison. This is **not** a full double-double precision pi
constant: its useful enclosure precision is limited by the twenty-decimal source
bounds. Decoding the three specified finite constants remains an instance of the
existing trusted constant-decoding boundary.

## Reduction and proof invariant

[SplitReductionProgram.lean](SplitReductionProgram.lean) reuses the existing
directed coefficient generation. The new native client uses 40 levels per sign,
with coefficients descending from 2^40 to 2. Each coefficient encloses twice an
integer. For an accepted coefficient C:

1. Subtract `C * H` from the coarse residual using directed operations.
2. Add `C * [Tlo,Thi]` to a separate correction interval.
3. After all selected shifts, subtract the accumulated correction once and
   invoke the existing sine kernel/global fallback.

Rejected shifts leave both states unchanged. Selection uses only the coarse
shift and remains a precision heuristic, not a correctness premise. A primitive
failure aborts the refinement; the outer proved global bound handles it for
supported finite input. NaNs, infinite endpoints and reversed intervals remain
unknown. Existing clients are unchanged; `sineUnsplit40` is a comparison client
using the same search depth with the previous pi bracket.

[SplitReduction.lean](SplitReduction.lean) proves `sweepSplit_sound` for the
function `sin(x-y)` on the coarse and correction states. Updating the states
changes their difference by exactly an integer multiple of 2*pi because the
same integer witness is used for both products and `H + (pi-H) = pi`.
`splitRun_sound` proves the complete coefficient-generation and sweep program
with an initially zero correction. No claim that native subtractions happen to
be exact is needed. The global fallback theorem remains applicable.

## Observed coverage and limits

Tests cover points and quarter-unit intervals spanning [-2^40,2^40], including
positive and negative one trillion. At x = 10^12 the native split result was

```
[-0.6112491950731197, -0.611238638566634]
```

Its width was about `1.056e-5`, versus `1.224e-4` for the unsplit 40-level
comparison. These are measurements, not universal precision guarantees. All
134 tested narrow cases had width below 0.5. The local Taylor approximation
still limits point accuracy even when reduction is much tighter.

The sum of positive coefficient magnitudes is 2^41-2. Multiplying that by the
proved tail-width bound gives a pre-rounding scale below about 2.21e-8; this is
not a final output-width theorem. Actual coefficient and arithmetic enclosure
widths also matter. Very large inputs outside the bounded sweep, wide intervals,
or failed refinements can still return [-1,1]. The enclosure-only contracts do
not guarantee native refinement success. All-binary64 accurate reduction and
correctly rounded sine remain open work.

Native IO/FFI/compiler/hardware refinement and existing directed-operation,
comparison and finite-selection contracts remain trusted. No general software
multiprecision runtime is added. External input domains and holes are not filled
by successful numeric evaluation.

## Source and validation

Tupper §3.1.5, printed pp.47–48
([PDF page 63](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=63)), discusses
high-precision constants for large arguments and interval reduction before a
local approximation. The split accumulator is our construction following that
principle, not a transcription of his fractional-part algorithm or a claim that
his complete large-argument treatment has been formalized. See the
[dyadic reduction](HARDWARE_SINE_DYADIC.md) and
[original source comparison](HARDWARE_SINE_REDUCTION.md).
The initial C target remains
[`gi_trans_sin`](https://github.com/funge/relgraph/blob/3975a5e1696e59c337093435ffce0748f074a057/src/transcendental.c#L644);
no equivalence to its MPFR implementation is proved. Its private source link is
not a build dependency.

`./check.sh` checks the proof and axiom allowlist. The independent Lean fixture
exercises multiple accumulated corrections, skipped shifts, correction/final
subtraction failures, and the unsoundness of dropping the tail.
`./hardware/check.sh` retains all earlier vectors and adds 138 split/unsplit
comparisons. Exact directed simulation checks both algorithms. An independent
Machin-pi/series oracle verifies the constants and nine samples per bounded
interval; it does not use the runtime pi bracket or shift choices for its analytic
comparison. Test-only rational arithmetic is not runtime arithmetic.
See [VALIDATION.md](VALIDATION.md) for qualification and trust limits.
