# Rational sequences and digit representations

This is one proof-only package for Tupper §§2.15.2, 2.15.3 and 2.15.6. The
original PDF was checked at printed p.41 / PDF p.57 and printed p.43 / PDF p.59.
The local Markdown omits §§2.15.4–8, so the signed-digit claims were read directly
from the PDF. Public source: [thesis p.41](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=57)
and [p.43](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=59).

## §2.15.2: actual representatives and operations

The source represents a real by a converging sequence of rationals, defines
operations termwise, and requires independence of the chosen representative.
[SequenceRepresentations](SequenceRepresentations.lean) gives this exact
interpretation as `Represents u x := Tendsto (fun n => (u n : Real)) atTop (nhds x)`.
It proves limit uniqueness and termwise addition, subtraction and multiplication.
The generic `lift_binary` theorem requires a real operation continuous at the
limiting pair and agreement with rational casts; `independent` then proves equal
output values for different input representatives of the same reals. The source's
generic operation symbol is not permission to inherit arbitrary discontinuous
or partial operations without these obligations.

Division has a nonzero limiting denominator premise. Its theorem proves
**eventual** nonzero rational denominators and the quotient limit. It does not
assert that every early term is defined. The rational field's totalized quotient
can describe the irrelevant finite prefix, but is not a claim of defined real
division at those stages. Guarded expression-stream convergence belongs to a later review unit; no
expression evaluator is introduced here.

This is connected to the actual pinned mathlib construction, not a new model
postulated to be the reals. `construction` uses `Real.of_near` to prove that any
converging rational stream is a rational Cauchy sequence whose `Real.mk` equals
its stated limit. `quotient_equality` and `quotient_operations` directly reuse
`Real.mk_eq`, `Real.mk_add`, `Real.mk_mul`, and `Real.mk_neg`. The underlying
quotient construction is supplied by mathlib; our correspondence and arithmetic
on raw rational sequences are kernel-checked here. No executable selector of a
representative for an arbitrary real is claimed.

[Sequence controls](tests/SequenceRepresentations.lean) include different streams
for zero, actual termwise multiplication, a three-stage zero prefix before safe
division, and arbitrary finite delays. The latter disproves a uniform stopping
index inferred solely from convergence; it is not an uncomputability theorem.
For u_n=(1/2)^n, both u and the zero stream represent zero, while u_n/u_n represents
1 and 0/u_n represents 0. This proves the zero-limit division premise matters,
even though every sampled denominator is nonzero. It does not assign a value to
real 0/0.

## §§2.15.3 and 2.15.6: infinite sums, not finite examples

[DigitRepresentations](DigitRepresentations.lean) uses an integer base b≥2 and
integer digits d_n. Index n corresponds to the source digit d_(n+1). The real
term is d_n (1/b)^(n+1). For every stream with |d_n|≤b−1 it proves:

- absolute summability and a represented value in [−1,1];
- rational finite partial sums converge to that value, hence supply a concrete
  rational-sequence representation under the preceding interpretation;
- the derived quantitative bound `|value - partialSum N| ≤ (1/b)^N`;
- termwise digit addition gives the sum of values **before carrying**, and
  negation gives the negative value.

Ordinary digits 0≤d_n<b specialize to values in [0,1]. The integral signed-digit
condition −b<d_n<b in §2.15.6 is proved equivalent to the absolute-value bound.
This is a normalized fractional representation; arbitrary magnitudes require
additional place/sign conventions, not a consequence of our range theorem.
For supplied computable digit streams, `partialSum` is finite rational arithmetic;
the real infinite sum is a mathematical interpretation, not a runtime evaluator.

The general `terminating_value` and `repeating_value` theorems prove the exact
infinite identity 0.100… = 0.0(b−1)(b−1)… = 1/b for all b≥2. This is not a
finite approximation. The source explicitly favors the zero-tail form. We do
not infer a contradiction from its “second form” phrasing: the displayed equation
also includes 0.1. Digit extraction and proof of a canonical representation's
existence/uniqueness remain open.

[Digit controls](tests/DigitRepresentations.lean) instantiate base 10's duplicate
expansion, zero, the all-negative expansion of −1, an alternating signed stream,
and ordinary endpoints. Adding two all-one binary expansions gives value 2 but
raw digit 2, outside the base-2 digit alphabet: the sum identity does not implement
carrying. A nonzero signed digit stream represents zero, as permitted by redundancy.
The exact four-digit binary prefix is 15/16 with error 1/16. Base 1 is excluded
for a genuine reason: its constant unit terms are not summable. A totalized `tsum`
for such invalid input is not a valid representation.

## What moved, and what did not

Checked: §2.15.2 termwise continuous arithmetic, representative independence and
actual Cauchy-quotient correspondence; §§2.15.3/6 bounded integer-digit sum
semantics, partial-sum convergence, arithmetic before carrying, signed convention,
and the explicit duplicate-expansion identity. The truncation bound is a derived
result, not a claim that Tupper states a rate for arbitrary rational streams.

Still open: canonical ordinary digit generation/uniqueness, carrying algorithm,
place/exponent normalization for all reals, signed-digit online algorithms and
circuit-delay claims, and redundant continued-fraction claims (§2.15.7). The supported §2.15.4
canonical conversion and its remaining limits are in
[continued-fraction conversion](CONTINUED_FRACTION_CONVERSION.md).
These are not marked covered by our finite fixtures or by the generic convergence
lemmas. No FP assumption, native path, hardware implementation, speed claim is added.
