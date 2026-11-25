# Generated affine reciprocal domain pieces

[AffinePoleSplit.lean](AffinePoleSplit.lean) extends the
[successful whole-hull composition](GUARDED_PIECE_COMPOSITION.md) with an exact
operation-domain construction that does not require that evaluator to succeed.
For a rational endpoint-basis affine denominator `d` and an existing finite guard
`g`, it appends `d(t)<0`, `d(t)=0`, or `0<d(t)` to form three disjoint, exhaustive
pieces. Equality is encoded by two non-strict affine inequalities. Existing open
and closed guard boundaries are retained. This works for constant denominators,
empty external domains and parameters outside the unit interval as well; any
restriction to `[0,1]` is explicit in the input guard.

The negative and positive pieces compile through the existing finite-guard
compiler. `admitted?` is an executable rational-input test, and `admitted_exact`
proves it true exactly when the partial reciprocal has a real value at that
parameter. `zero_absent` separately records the undefined piece.
`graph_split` is equality of partial value relations at the **same** parameter and
output. `expression_exact` connects that relation to the existing `Expr.Value`
division constructor. No new AST, totalized division semantics, arbitrary
coefficient re-choice, or inferred native execution is introduced.

## A pole is not a finite range

The [kernel-checked fixture](tests/AffinePoleSplit.lean) uses `0 ≤ t ≤ 1`,
`d(t)=t−1/2`. The existing finite guarded evaluator returns unknown on the whole
hull. The generated domain nevertheless accepts exactly the nonzero-denominator
parameters, with the original endpoints retained and `t=1/2` explicitly
undefined. Reusing `SplitQuotient.reciprocal_image`, the fixture proves the exact
attainable image `(-∞,-2] ∪ [2,∞)` and both attained tips. Its unboundedness
theorems construct actual values beyond every finite proposed lower/upper bound.
These infinities describe sets of finite real values, not literal infinite
coefficients or λ-valued evaluations.

Additional controls cover open external endpoints, constant zero/positive/negative
denominators and a false separate-witness repair of the pole. The rational
executable control returns `[true,true,false,true,true,false]` at
`[0,1/4,1/2,3/4,1,2]`. Exact classification does not claim a finite value enclosure
on either piece near the pole, automatic evaluator success, or a deployed split
backend. It also does not certify uncertain denominators from their marginal
hulls: each affine denominator is a fixed function of the original parameter.

## Source correspondence and remaining work

Tupper [thesis §2.11.4, printed pp.35–36 / PDF pp.51–52](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=52)
says a partial operation introduces its own domain constraint in addition to the
input conjunction. The three finite affine pieces here are a derived constructive
instance using the project's explicit guard grammar, not a claim that the thesis
specifies this compiler. §2.13 motivates retaining sets. The direct two-ray
reciprocal source is [SIGGRAPH 2001 §11, p.82 / PDF p.6](https://www.dgp.toronto.edu/papers/jtupper_SIGGRAPH2001.pdf#page=6);
the thesis's crossing-zero reciprocal display instead uses the whole hull.
See [the existing split-quotient source distinction](SPLIT_QUOTIENT.md).

This closes a restricted operation-generated domain split. General composition of
unbounded value pieces, nonlinear zero sets, uncertain coefficient families and
unspecified exceptional operations remain separate obligations in the
[closeout matrix](CHAPTER2_CLOSEOUT.md). No floating-point premises, hardware
contract, native code or default evaluator changes occur. Run `./check.sh` for
the full local gate; focused checks are `lake build AffinePoleSplit` and
`lake env lean tests/AffinePoleSplit.lean`.
