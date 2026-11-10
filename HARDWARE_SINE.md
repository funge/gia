# Hardware sine enclosure on [-1, 1]

This milestone implements a restricted sine enclosure by composing the existing
hardware-backed directed addition, subtraction, multiplication and division.
It is general arithmetic, with no graphing, pixel or rendering assumptions.
It does not call or trust a system `sin`, and it does **not** compute correctly
rounded sine. Argument reduction and inputs outside [-1, 1] remain
unsupported; returning `none` means unknown, not an undefined sine value.

## Source and precise mathematical claim

Tupper's thesis §3.1.6, printed pp.48–49
([original PDF, page 64](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=64)),
describes the fifth-degree sine polynomial and a seventh-order remainder,
then evaluates these with interval arithmetic. The equations on both pages were
visually checked against the repository PDF copy; the Markdown transcription is
not the authority. The thesis allows [0, π/2); this implementation deliberately
uses the smaller [0, 1] domain and no π approximation or reduction.
The original positive evaluator also accepts nonsingleton intervals in [0, 1].
The current endpoint client extends support to [-1, 1] using odd symmetry and
monotonicity, rather than extending the Taylor theorem beyond its proved domain.

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

## Monotone endpoints and odd symmetry

[SineEndpoints.lean](SineEndpoints.lean) proves sine monotone on [-1, 1] from
mathlib's theorem on [-π/2, π/2] and 2 ≤ π. This specializes the monotone endpoint
bounding principle in Tupper §3.2.10 and lower-bound construction in §3.2.12,
printed pp.56–57
([PDF page 72](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=72)); the
original pages were visually checked. We do not claim to formalize that section's
full generalized real/domain construction here.

The native `sineEndpoints` client evaluates the two endpoints separately and
assembles the lower bound of the lower endpoint with the upper bound of the
upper endpoint. A negative point is reflected by directed `0 - [x,x]`, evaluated
with the positive Taylor program, and reflected back by directed subtraction.
`Real.sin_neg` justifies this mathematically. No exact native negation, libm sine
or additional floating-point assumption is introduced. The constant -1 uses the
same explicit exact-decoding obligation as 0 and 1. The input guard rejects
nonfinite, reversed or out-of-range inputs. Any operation failure returns unknown.

`positive_run_sound`, `signedPoint_encloses` and `signed_endpoints_enclose` connect
the existing primitive contracts to the new complete path. The proofs quantify
over every enclosed real input. They do not infer domain existence from successful
numeric calculation. The original positive natural-interval client is retained
for comparison, not silently replaced or generalized.

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
The endpoint client reduces the ideal [0, 1] result to [0, 101/120], of width
101/120 (about 0.84167). `ideal_endpoint_bounds` proves this construction for
all nonnegative subintervals; `ideal_endpoint_improves_natural` proves inclusion
in the ideal natural-interval bounds. At a point, the analytic approximation
width remains |x|⁷/5040. This change removes interval dependency overestimation;
it does not increase the polynomial degree. General native subset/width claims
do not follow from enclosure-only contracts, which permit loose adapters; native
precision comparisons below are observed tests, not a universal refinement proof.
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
point intervals and nonsingleton intervals. Its 39 positive natural-interval vectors and 73 signed endpoint vectors are
checked by [an independent exact-arithmetic oracle](hardware/check_sine.py),
including both directed-rounding simulation and analytic bounds. It never calls
libm sine. The signed oracle checks nine analytic samples per input interval,
exact simulated directed operation results, and observed inclusion in the old
natural-interval bounds on nonnegative test inputs. Lean controls include signed
composition through an independent real oracle, failed reflection/upper endpoint,
external holes, and the counterexample sin(π/2) > sin(π) prohibiting global
monotone extrapolation. Rational arithmetic is confined to this independent **test oracle**,
not the executable interval algorithm. Neither finite test coverage nor the
object-code instruction checks prove the adapter contract universally.

See [VALIDATION.md](VALIDATION.md) for the qualification receipt and observed widths.
