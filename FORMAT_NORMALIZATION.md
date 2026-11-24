# Uniform format separation and general-radix normalization

The original Tupper §2.5 displays were checked visually on printed pp.18–19 / [PDF pp.34–35](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=34), including the surrounding parameter and sign discussion. The coefficient formula has strict bound `|a| < b^(A−1)` and shifted exponent `m ≤ c+(A−1) ≤ M`. The next display uses `A` unsigned base-`b` digits with radix point after the leading digit and `m ≤ e ≤ M`. The prior [format distinction](FORMAT_DIGITS.md) remains unchanged. External mathematical feedback suggested the uniform witness; the source images and Lean proof, not that feedback, establish the result here.

## A uniform separation, not just a single example

For every existing `FiniteFormat.Format` (`b ≥ 2`, `A ≥ 1`, `m ≤ M`), [FormatNormalization.lean](FormatNormalization.lean) proves:

- `literal_upper`: every value of the literal coefficient formula is strictly below `b^M`. For nonnegative values this reuses the earlier local `literal_below` and exponent monotonicity; negative values are strictly below the positive witness too.
- `upper_digit_witness`: packed magnitude `b^(A−1)` at exponent `M` is normalized, is admitted by the unsigned digit display and evaluates exactly to `b^M`, which is absent from the literal coefficient set.
- `strict_repair`: the literal coefficient set is a proper subset of the separately labeled signed repaired format, using the prior inclusion theorem.

Thus the two literal displays cannot have equal finite value sets under these conventions for any admitted parameters. This does not say their sets are disjoint, identify the intended correction, or refute IEEE 754. The positive witness does not rely on the missing external sign in the digit display.

## Exact value-set normalization of the labeled repair

`shift_digit` preserves value when multiplying the packed magnitude by `b` and decreasing the exponent by one. `shifted_admitted` proves the magnitude stays within `A` digits whenever its previous leading digit was zero. `normalize_distance` inducts on the finite distance to minimum exponent, stopping once normalized or at that minimum. `normalize` covers every admitted magnitude/exponent, including zero and negative exponent ranges.

`repaired_iff_normal_or_minimum` proves, at **arbitrary radix**, equality of the unrestricted repaired value set and the separately labeled normal-or-minimum convention, with the same external sign. This is equality of values, not representations, uniqueness, an executable normalizer, exact hardware rounding, or an IEEE encoding theorem. It neither modifies the literal source definition nor attributes the minimum-exponent convention to the printed digit display.

The earlier `minimum_not_normalizable` still applies: a leading-zero magnitude already at the minimum exponent need not admit any normalized representation in range. Retaining that minimum case is essential, not a shortcut in the proof.

## Controls and remaining scope

[Kernel fixtures](tests/FormatNormalization.lean) check precision one, a singleton exponent range, negative maximum exponent, nonbinary radix, multiple shifts, external negative sign, zero, and a minimum-exponent denormal that cannot normalize. They also demonstrate that the presentation changes even though the value does not.

Run `./check.sh`; see [VALIDATION.md](VALIDATION.md). No new project axioms, FP assumptions, native/default changes or hardware execution are involved. Rounding exceptional values, tie rules and authorial intent remain separate. This closes the general-radix value-set normalization gap without claiming Chapter 2 complete.

Public-source review question: do the printed pages supply any additional convention that excludes the leading-digit-one witness at maximum exponent, or changes the literal strict coefficient bound? Our formal result keeps both printed definitions fixed and treats the larger signed format as an explicitly labeled repair.
