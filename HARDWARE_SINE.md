# Hardware sine enclosure on [0, 1]

This milestone implements a restricted sine enclosure by composing the existing
hardware-backed directed addition, subtraction, multiplication and division.
It is general arithmetic, with no graphing, pixel or rendering assumptions.
It does not call or trust a system `sin`, and it does **not** compute correctly
rounded sine. Argument reduction, negative inputs and inputs above one remain
unsupported; returning `none` means unknown, not an undefined sine value.

## Source and precise mathematical claim

Tupper's thesis §3.1.6, printed pp.48–49
([original PDF, page 64](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=64)),
describes the fifth-degree sine polynomial and a seventh-order remainder,
then evaluates these with interval arithmetic. The equations on both pages were
visually checked against the repository PDF copy; the Markdown transcription is
not the authority. The thesis allows [0, π/2); this implementation deliberately
uses the smaller [0, 1] domain and no π approximation or reduction.
The native client also accepts nonsingleton intervals wholly inside that domain,
extending the displayed singleton construction by interval inclusion.

[SineTaylor.lean](SineTaylor.lean) proves, for 0 ≤ x ≤ 1,

```
P5(x) = x - x³/6 + x⁵/120
P5(x) - x⁷/5040 ≤ sin(x) ≤ P5(x)
0 ≤ x⁷/5040 ≤ 1/5040.
```

The proof uses mathlib's real sine power series and alternating partial-sum
bounds; it proves the remainder inequalities rather than assuming the thesis's
existential ξ representation. This is a narrower-domain counterpart of the
source result, not a literal transcription of its proof. No Taylor remainder
or transcendental-correctness axiom is added.

## Execution and proof boundary

[SineProgram.lean](SineProgram.lean) is one shared monadic straight-line program:
it forms X², X³, X⁵ and X⁷, divides by exactly representable 6, 120 and 5040,
evaluates X − X³/6 + X⁵/120, and subtracts [0, upper(X⁷/5040)].
The native wrapper first rejects nonfinite endpoints, then checks
0 ≤ lower ≤ upper ≤ 1. Every failed operation propagates `none`.

[HardwareSine.lean](HardwareSine.lean) proves the pure specialization's enclosure
under explicit operation contracts, and discharges those contracts from the
existing directed-primitive assembly theorems. The range guard uses the existing
finite comparison contract. Exact decoding of zero, one and the three small
integer constants is explicit. As before, Float decoding, native comparisons,
correct directed primitive operations, the IO/FFI connection and compiler/hardware
behavior are trusted boundary obligations, not kernel-verified implementation facts.
The proof does not assert that a Lean logical fallback equals a C extern.
The IO specialization executes the same shared program with the existing adapters.
Native qualification is on x86_64 binary64, using FE_DOWNWARD/FE_UPWARD; the
existing adapter rejects flush-to-zero and denormals-are-zero modes.

`SinValues` retains the same input witness and arbitrary external domain relation.
Sine itself is total on real values: an external hole stays a hole, while failure
of this restricted implementation makes no domain classification. Successful
numeric enclosure does not create a witness or prove an external domain nonempty.

## Precision and limits

The analytic point approximation width is x⁷/5040, at most 1/5040
(about 0.0001984126984). This is **not** a uniform bound on the final computed
interval width. Hardware rounding adds error, and a nonsingleton interval also
incurs dependency overestimation from repeated occurrences of X. For example,
the ideal natural interval on [0, 1] is [-841/5040, 121/120], of width
5923/5040 (about 1.1752); a Lean regression checks this nonsingleton case.
This first implementation does not exploit sine monotonicity to narrow that range.
No quantitative IEEE rounding-error theorem is claimed by these enclosure-only
contracts. The native test records actual widths separately.

This is an algorithmic alternative to relgraph's
[`gi_trans_sin`](https://github.com/funge/relgraph/blob/7fd4b39dc127dec3be1b96a46cf392d4bcd73d2b/src/transcendental.c#L645),
whose implementation uses MPFR and periodic phase/extremum handling. The matching
[public API](https://github.com/funge/relgraph/blob/7fd4b39dc127dec3be1b96a46cf392d4bcd73d2b/include/graphing/transcendental.h)
is an initial comparison target; these private-repository links may require access.
No correspondence proof to that C algorithm is claimed and no C library is copied.
The unchanged [demo FFI adapter](hardware/adapter.c) is GIA support code.

## Verification

Run `./check.sh` for the pinned Lean build, enforced axiom audits and independent
semantic fixtures; run `./hardware/check.sh` for actual native execution.
The native suite checks unsupported inputs, signed zero, subnormal inputs,
point intervals and nonsingleton intervals. Its 39 supported sine vectors are
checked by [an independent exact-arithmetic oracle](hardware/check_sine.py),
including both directed-rounding simulation and analytic bounds. It never calls
libm sine. Rational arithmetic is confined to this independent **test oracle**,
not the executable interval algorithm. Neither finite test coverage nor the
object-code instruction checks prove the adapter contract universally.

See [VALIDATION.md](VALIDATION.md) for the qualification receipt and observed widths.
