# Redundant signed continued fractions

This proof-only milestone treats the infinite class displayed in Tupper
§2.15.7, printed p.43 / [PDF p.59](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=59).
The original page image was checked, including the finite last-term rule. The
local Markdown transcription omits this subsection. §2.15.4 is the ordinary
simple representation; §2.15.8 discusses generalized interval arithmetic.

## Source restrictions and proved scope

For an infinite integer stream `a`, the head is unrestricted. Every tail term
has absolute value at least 2. Whenever `|a(n+1)| = 2`, the product
`a(n+1)*a(n+2)` is strictly positive. These are `RedundantCF.Admissible` in
[the module](RedundantCF.lean). There is no last term in an infinite stream.

The theorem `suffix_limits_exist` proves convergence for **every** such stream,
including sign-changing, unbounded and noncomputable coefficient streams.
It does not assume convergence, periodicity, positivity of all coefficients,
or a supplied limit. `unique_value` proves a unique real limit for the same
stream; it does **not** prove uniqueness of the coefficient presentation.

The observations reuse `InfiniteSimpleCF.trunc` and are bridged by
`finite_prefix` to the existing rational `finiteValue` evaluator. Thus they
are ordinary nested simple-fraction observations, not a new generalized
numerator convention. All finite observed suffix divisors and all limiting
suffix divisors are proved nonzero. `limits_recurrence` gives the recursive
real interpretation of the limiting suffixes. Lean's totalized division at
zero does not supply definedness for this theorem.

The proof first establishes a sign-sensitive invariant: each fractional tail
is in `[-1/2,1/2]` and has the sign of its leading coefficient (or is zero).
When the leading magnitude is 2, the adjacent-sign rule makes the next
fraction reinforce it; when it is at least 3, the half-unit bound suffices.
On that invariant, each reciprocal step contracts by at most `4/9`.
Completeness of the real numbers then gives all suffix limits.
`limit_error` proves an error bound `(4/9)^N` after `N` further terms. This
is a derived bound, not a verbatim source rate. Computable supplied coefficients
give executable rational observations; arbitrary coefficient computability is
not a premise or conclusion of the existence theorem.

Negating the **same** entire coefficient stream negates every observation and
its represented value. On the positive ordinary-simple overlap,
`positive_recovery` reuses the earlier canonical theorem to recover the actual
mathlib `GenContFract.of`, irrationality and its convergent limit. No equality
with that canonical positive-tail expansion is claimed for negative tails.
The signed theorem is stated for nested finite observations, not an unproved
identity with every mathlib generalized-continuant algorithm.

## Finite conventions and remaining extraction obligation

The printed finite restrictions apply the magnitude and adjacent-sign tests
only before the last term; the last term is required to differ from `-2`.
`FiniteTail` records precisely those tests. They intentionally do not include
an invented last-term magnitude bound. The fixtures check two different
permitted finite tails, `[3]` and `[2,1]`, both representing `1/3` with head 0.
Finite redundancy must not be replaced by a universal canonical-uniqueness
claim.

Those printed syntactic tests alone also admit `[3,0]`, whose innermost real
division would have denominator zero. The fixture records the syntactic fact
and zero suffix separately; it does not promote Lean's totalized rational
value to a source-valid real evaluation. This is a missing finite admissibility
or extraction premise, not a guessed exceptional-arithmetic rule or an assertion
about the author's intended algorithm.

The page says an interval variant of Euclid's algorithm determines terms and
references software, but supplies no extraction pseudocode or rewrite system.
This milestone does **not** prove that every real has a signed representation,
a complete extraction algorithm, irrationality of every signed infinite stream,
or uniqueness/recovery of all signed digits. Those remain separately stated
correspondence obligations. It also does not cover arbitrary signed streams:
the fixture with leading `2,-2` violates the adjacent-sign condition and
already exceeds the proved half-unit invariant.

## §2.15.8 and chapter scope

The next subsection says GIA **can** improve convergence over constant intervals,
notes that symbolic intervals converge immediately but unproductively, and
refers functional-bound benefits to later graphing chapters. It supplies no
universal strict-improvement theorem, numerical rate or prescribed algorithm.
Existing same-witness functional/symbolic semantics support the framework;
particular quantitative improvement claims require particular operations.
This observation does not close remaining family/conversion proof gaps or
justify calling Chapter 2 complete. See the [section ledger](SECTION215_LEDGER.md)
and [closeout matrix](CHAPTER2_CLOSEOUT.md).

## Verification and trust

Run `./check.sh` with the pinned Lean toolchain. The focused command is
`lake env lean tests/RedundantCF.lean` after `lake build RedundantCF`.
[Fixtures](tests/RedundantCF.lean) cover positive/negative 2 tails, alternating
signed 3 tails, finite prefixes, nonzero divisors, error bounds, positive
canonical agreement, finite nonuniqueness and the terminal-zero limitation.
The executable alternating prefix is `0, -1/3, -3/8, -8/21`.

No project axioms, floating-point assumptions, native adapter, C arithmetic,
production defaults or dependencies change. These are mathematical real/rational
proofs; they are not a hardware continued-fraction implementation.
