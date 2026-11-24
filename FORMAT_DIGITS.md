# Coefficients, digits and the minimum exponent

[FormatDigits.lean](FormatDigits.lean) compares the two displays in Tupper §2.5,
printed pp.18–19 / [PDF pp.34–35](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=34).
Both pages were inspected visually, including the surrounding IEEE example and
parameter discussion. The previous [literal format](FINITE_FORMAT.md) is unchanged.

## What the pages say

The coefficient display uses signed integers `a,c`, strict magnitude bound
`|a| < b^(A−1)`, and `m ≤ c+(A−1) ≤ M`. The next display uses `A` digits
`d₀.d₁…d_(A−1) × b^e`, each `0 ≤ dᵢ < b`, with `m ≤ e ≤ M`.
It calls `d₀ ≠ 0` normalized and `d₀ = 0` denormalized, and asserts that the
displays describe the same system. No external sign appears in the second
display. The preceding binary64 paragraph describes 53 bits as 52 magnitude
bits and one sign bit. These conventions do not justify silently identifying
the two displayed sets, or identifying either with our IEEE decoder.

## Exact relationships proved

We use an unsigned packed magnitude `n < b^A`. `digit_list` proves this is
exactly a base-`b` list of at most `A` digits with every digit below `b`, using
mathlib's actual `Nat.digits` and `Nat.ofDigits`. Mathlib lists are least-digit
first; omitted leading positions are zero. `radix_point` proves the value is
`(n / b^(A−1)) * b^e`, equivalently `n * b^(e−(A−1))`.

The leading digit is `n / b^(A−1)`. It is below `b` for admitted magnitudes,
and nonzero iff `b^(A−1) ≤ n`. `normalized_iff` characterizes a normalized
presentation by `b^e ≤ value < b^(e+1)`. This is a test on discrete digit
presentations, **not** a claim that every real in that binade is representable.

`literal_nonnegative` exactly reindexes the nonnegative part of the original
coefficient formula: it instead has `n < b^(A−1)`. `literal_below` proves its
value lies below `b^e` at the same exponent. These local distinctions do not
imply disjoint projected sets when different exponents are allowed.

At minimum exponent `m`, every normalized presentation with exponent at least
`m` has value at least `b^m`. Therefore a leading-zero presentation at `m`
cannot be replaced by any such normalized presentation (`minimum_not_normalizable`).
The fixture `0.1 × 10^1 = 1.0 × 10^0` shows why exponent freedom matters above
that boundary. The later [general-radix normalization proof](FORMAT_NORMALIZATION.md) establishes existence and value-set equality; no executable normalizer is claimed.

## A labeled repair, not authorial intent

`Repaired` explicitly supplies an external sign and `A` magnitude digits.
`repaired_coefficients` proves exact equivalence with signed integer coefficients
bounded by `b^A`, keeping the exponent shift `A−1` unchanged. Every literal
coefficient value belongs to this repaired family. It is a mathematical repair
choice; it does not redefine `FiniteFormat` or establish an IEEE correspondence.

`NormalOrMinimum` is a separately labeled convention allowing leading-zero
magnitudes only at `m`. The theorem `minimum_admitted` shows what it admits;
we do not attribute this restriction to the printed display (which allows
leading zeros at other exponents too). The later
[general-radix theorem](FORMAT_NORMALIZATION.md) proves equality of the repaired
value sets, while preserving this distinction. No IEEE subnormal/overflow/tie
behavior is inferred.

## Sharp controls and limits

[Kernel fixtures](tests/FormatDigits.lean) include decimal `(b,A,m,M)=(10,2,0,0)`:
`1.0` is in the repaired digit family but not the literal coefficient family;
`0.1` is literal but has no normalized presentation in the allowed exponent
range; `−0.1` is literal but cannot be expressed by the unsigned digit display.
They also check leading zero, the smallest normalized coefficient, the largest
admitted coefficient, rejection at `b^A`, and an actual digit-list roundtrip.

Run `./check.sh`. Proofs and fixtures use the existing axiom allowlist. No new
axioms, floating-point premises, hardware changes, native conversion, signed
zero semantics or rounding algorithm are introduced. The full IEEE model
correspondence and any claim about the author's intended correction remain open.

## Public-source review question

In Tupper §2.5, printed pp.18–19 (PDF pp.34–35), is there a stated convention
that reconciles `|a| < b^(A−1)` with the unsigned `A`-digit display at the same
exponent limits? For `(10,2,0,0)`, the latter admits `1.0` and the former does
not. Does adding an external sign and changing only the coefficient bound to
`b^A` correctly repair the displayed finite-value correspondence, while leaving
minimum-exponent normalization and IEEE identification as separate questions?
