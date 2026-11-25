# Ordinary digit extraction and canonical reconstruction

Tupper §2.15.3, printed p.41 / [PDF p.57](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=57), defines base-b digit sums, displays the terminating/repeating ambiguity and prefers the zero-tail representation. The original page was visually checked. [The full §2.15 ledger](SECTION215_LEDGER.md) distinguishes the remaining survey obligations.

[DigitExtraction.lean](DigitExtraction.lean) reuses the existing digit sum and rational partial-sum model. For an integer base b≥2 and x∈[0,1), define r₀=x, dₙ=floor(b rₙ), rₙ₊₁=fract(b rₙ). The kernel proves:

- `digits_ordinary`: 0≤dₙ<b, with rₙ∈[0,1).
- `partial_remainder`: partialSum N + rₙ b^(−N)=x; convergence and `extraction_exact` follow without a new real-number model.
- `canonical_iff_tails`: an ordinary stream is canonical iff every shifted tail has value <1. Here canonical explicitly means that after every position there is a digit smaller than b−1, excluding exactly eventually maximal tails.
- `reconstruct`: extracting from the value of **any** ordinary canonical stream recovers that entire stream, not just its represented value.
- `canonical_unique`: equality of represented values iff equality of canonical streams.
- `all_real` and `representation_unique`: every real has a unique integer-part plus canonical fractional stream representation. Negative numbers and integers are included. This fixed radix-point convention is explicit; unrestricted floating-place/sign codes would need their own normalization.
- `terminating_tail`: once a remainder is zero, every later digit is zero.

The fractional endpoint 1 is represented by the all-maximal stream in the old sum semantics, but that stream is not canonical. The canonical all-real representation uses integer part 1 and zero fractional digits. Invalid bases and alphabets are outside the theorem, not silently repaired. The duplicate decimal 0.100…=0.099… remains true; only the former is canonical. No finite prefix test decides the infinite canonical condition.

[Fixtures](tests/DigitExtraction.lean) cover 1/10's zero tail, 1/6's prefix, negative −1/4's integer part and digits, all-base reconstruction, zero, 1, invalid digits, duplicate tails, and floating-place ambiguity. These are kernel proofs using exact real/rational arithmetic; there is no native digit-extraction experiment.

Real floor and the real input are **noncomputable** here. This proves mathematical representation and uniqueness, not an executable arbitrary-real oracle, online carrying, a finite extraction stopping rule, a hardware arithmetic path, or a new FP assumption. Existing computable rational streams/accuracy search retain their separate scope. A canonical representation of a sum exists by `all_real`; an effective carry algorithm with finite input access is a distinct obligation.
