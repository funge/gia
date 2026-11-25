# Arbitrary infinite simple continued fractions

The source is Tupper **§2.15.4**, printed p.42 / [PDF p.58](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=58), visually rechecked for this milestone. Redundant continued fractions are §2.15.7, not §2.15.8; §2.15.8 discusses GIA representations. Neither is silently folded into the simple positive case.

## Admissibility and actual representations

[InfiniteSimpleCF.lean](InfiniteSimpleCF.lean) takes an arbitrary stream `a : Nat → Int` with `0 ≤ a 0` and `1 ≤ a (n+1)` for every n. It has infinitely many coefficients, all partial numerators are one, and it has no final coefficient. The source's last-term ≥2 convention applies to finite normalized presentations, not to this stream. Coefficients need not be bounded, eventually periodic, or computable.

`presentation a` is an actual mathlib `GenContFract Real`, not a parallel continued-fraction representation. Rational `trunc a n k` evaluates the finite suffix beginning at n with k further coefficients. `trunc_finite` identifies it with the existing `ContinuedFractionConversion.finiteValue`; the previously proved finite semantics is reused. Temporary finite observations can end in 1 and need not be normalized finite codes. All their divisors are positive under admissibility, as follows from `trunc_bounds`.

## Existence is proved, not supplied

The proof separates steps that must not be conflated:

1. `fraction_range` bounds each fractional tail observation in [0,1].
2. `two_step` proves that two maps `t ↦ 1/(b+t)` with b≥1 contract differences by at least a factor of four. A single map need not have a strict uniform contraction.
3. `fraction_gap` proves `|fraction(n,2N+m)-fraction(n,2N)| ≤ (1/4)^N` for every m. This yields Cauchy convergence for each suffix. `suffix_limits_exist` uses completeness to produce all suffix limits; it does not assume them.
4. `limits_recurrence` passes the recurrence to these limits with explicit nonzero denominator bounds. `limits_quotients` sharpens the bounds to `a n < v n < a n+1`, including when a tail coefficient equals 1.
5. Floor/fract recovery proves every actual stored coefficient matches: `GenContFract.of (v 0) = presentation a`.
6. Irrationality follows from the existing rational-iff-termination theorem and the presentation's infinite sequence. Only after recovery do we reuse canonical `of_convergence` for the actual convergents. There is no circular invocation of canonical convergence to establish arbitrary-stream existence.

`admissible_reconstruction` therefore proves, for every admissible stream, existence of a positive irrational x, exact canonical recovery, and convergence of the actual mathlib convergents to x. `unique_value` proves the represented value is unique. `representation_unique` proves equality of represented values iff equality of every coefficient for two admissible streams. `represents_iff` connects convergence and canonical recovery under admissibility.

`limit_error` additionally proves `|v n - trunc(n,2N)| ≤ (1/4)^N`. This is a derived bound for this class, not a rate claimed verbatim by Tupper. Finite rational observations are executable when the supplied coefficient stream is computable; existence of limits and arbitrary real-input extraction are mathematical, not a native real oracle. No hardware, FP assumption, C/default path or dependency changes occur.

## Controls and scope

[Fixtures](tests/InfiniteSimpleCF.lean) check the all-one infinite tail (whose prefix is `0, 1, 1/2, 2/3, 3/5`), unbounded increasing coefficients, arbitrary coefficient recovery and uniqueness, the finite-evaluation bridge and a concrete accuracy bound. The prefix is both kernel-proved and actually evaluated.

An all-zero stream has convergent suffix observations but is inadmissible; its infinite presentation is not `of 0`. This is a checked failure of dropping admissibility, not a definition of valid division by zero. A negative redundant stream is outside this positive simple theorem. No arbitrary generalized numerators, signed redundant reconstruction, or uniqueness for redundant representations is asserted.

Together with the existing normalized finite reconstruction, rational termination equivalence and canonical irrational construction, this closes the previously identified **arbitrary admissible infinite simple-stream converse**. The [section ledger](SECTION215_LEDGER.md) retains the distinct redundant-fraction and algorithmic obligations; Chapter 2 as a whole is not declared complete.
