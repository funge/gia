# Bounded automatic sine period reduction

The native `sineDyadic` client replaces a fixed five-period search as the first
attempt with a bounded sweep of power-of-two whole-period shifts. Its purpose is
to obtain useful enclosures for narrow arguments around magnitude one million,
without trusting Float-to-integer conversion, floor, remainder, or a quotient
rounding rule. It uses existing directed hardware addition, multiplication and
subtraction, then the existing period/quadrant kernel and global fallback.

## Algorithm and proof

[DyadicReductionProgram.lean](DyadicReductionProgram.lean) is shared by the pure
proof and native IO instantiations. Starting from coefficient intervals [2,2]
and [-2,-2], `doubledPeriods` constructs 20 coefficients of each sign by directed
addition. Each list is reversed, giving descending magnitudes 2²⁰ through 2.
For a positive shift interval S, the native selector accepts only if I.lo ≥ S.hi;
for a negative shift, it accepts only if I.hi ≤ S.lo. Accepted shifts are
subtracted with directed interval arithmetic. Rejected shifts leave the residual
unchanged. A primitive failure returns unknown from this refinement attempt.
After the sweep, the existing `sineGlobal` client handles the residual. The outer
proved global fallback handles failed attempts for supported finite inputs.
NaNs, infinite endpoints and reversed intervals remain unknown.

[DyadicReduction.lean](DyadicReduction.lean) proves:

- `doubledPeriods_sound`: every generated coefficient encloses twice an integer.
  It does not require hardware doubling to be exact.
- `reverse_append_periods`: ordering and joining the two lists preserves these
  witnesses.
- `sweepPeriods_sound`: each accepted shift preserves the sine value, retaining
  the same real input witness through all interval operations.
- `dyadicRun_sound`: the actual generation, reversal, concatenation and sweep
  compose into a sound sine kernel.

The choice predicate is arbitrary in the soundness theorem. Incorrect or
unhelpful selection can widen the answer or cause fallback, but cannot turn a
non-period into a period. The coefficient witnesses are derived by proof from
directed addition; they are not assumed from an unchecked quotient or cast.
Termination of the pure finite recursion follows from Lean's structural
recursion. Native IO execution/refinement remains trusted as before.

## Coverage, precision and remaining work

The native client uses 20 levels, hence 40 candidate shifts. Tests exercise
points and quarter-unit intervals spanning [-2²⁰,2²⁰], including ±1,000,000.
This is a tested refinement range, not a proved guarantee that every native
input in it avoids fallback. The enclosure-only contracts permit loose results
and failure. Wide intervals and inputs beyond the sweep's effective range may
return [-1,1]. The returned bounds remain conservative at arbitrary finite
magnitudes through the existing global fallback.

Pi uncertainty is retained in every multiplication and subtraction. The sum of
the positive coefficient magnitudes is 2²¹−2. Multiplying that by the current
pi-bracket width 2⁻⁵¹ gives about 9.32×10⁻¹⁰ before operation rounding; this is a
scale estimate, not a proved final-width bound. The local Taylor approximation
still limits point accuracy. This is neither correctly rounded sine nor a
high-precision all-binary64 argument reducer. Larger arguments eventually need
a tighter pi representation and a separately justified reduction strategy.

No new FP assumptions or exact-arithmetic runtime were introduced. Exact decoding
of ±2, ±1 and the existing pi bracket, finite comparisons, directed primitives
and IO/FFI/compiler/hardware refinement keep their existing trusted status.
The selector's numerical correctness is unnecessary for enclosure soundness.
External domains are not enlarged; a numeric bound does not fill a hole.

## Source and implementation references

Tupper §3.1.5, printed pp.47–48
([PDF page 63](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=63)), describes
interval argument reduction and the difficulties of accurate large arguments.
This bounded dyadic sweep implements the periodicity/interval principle, not
his fractional-part formula or a claim to reproduce its complete coverage.
See the [earlier source comparison](HARDWARE_SINE_REDUCTION.md) and
[quadrant construction](HARDWARE_COSINE_QUADRANTS.md). The original PDF is the
authority; the known Markdown half/quarter transcription defect is not used.

The initial C comparison remains
[`gi_trans_sin`](https://github.com/funge/relgraph/blob/3975a5e1696e59c337093435ffce0748f074a057/src/transcendental.c#L644).
That private implementation uses a different algorithm. No C correspondence is
proved and GIA does not depend on its checkout for normal builds.

## Verification

Run `./check.sh` and `./hardware/check.sh`. The Lean fixture covers generated
coefficients, generation failure, rejected shifts, accepted-operation failure
and a deliberately unhelpful period. The native suite checks 138 new vectors,
with exact directed-operation simulation and nine samples per bounded interval.
Its independent analytic oracle derives a much tighter pi bracket from Machin's
formula, outward-compresses it to 160-bit dyadics, reduces with test-only rational
arithmetic, and uses a sine series plus a Lipschitz error bound. It does not reuse
the runtime pi constants or the greedy shift choices for the analytic comparison.
Huge-input controls check the exact global fallback rather than an unreliable
large-angle series. Test-only rational arithmetic is not the deployed runtime.
All existing native tests remain enabled. See [VALIDATION.md](VALIDATION.md).
