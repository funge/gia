# Composing guarded unbounded real pieces

[UnboundedPieceComposition.lean](UnboundedPieceComposition.lean) reuses the
[finite half-space pieces](FINITE_GUARD_PIECES.md). A finite description need not
have bounded fibers: a ray is one output inequality. No new interval framework,
expression AST, native representation or exceptional arithmetic table is added.

## Exact representation operation

`shiftAtom` substitutes `z-s(t)` into an existing rational affine half-space for a
rational affine `s`, retaining the strict/open boundary bit. `shift` maps this
through the existing list of conjunction pieces. `shift_image` proves exactly

```text
pieces (shift s cs) t = {v + s(t) | v ∈ pieces cs t}.
```

The parameter is the same on both sides. This applies to bounded or unbounded,
open or closed, empty or disconnected fibers. `shift_guard` additionally proves
that the original parameter-only guard atoms are structurally unchanged.
`shift_nonempty` and `shift_empty` preserve domain holes. `shift_encloses` composes
this exact representation operation with any previously proved enclosure; it
does not upgrade an enclosure to an exact expression image.

## A reciprocal followed by addition

`reciprocalCode` encodes two rays in that same representation, retaining the
negative and positive guards from [affine pole splitting](AFFINE_POLE_SPLIT.md).
Given actual bounds `l ≤ d(t) ≤ u` on every admitted parameter, every defined
reciprocal belongs to the appropriate ray (`reciprocal_encloses`). The numerical
premise is essential and is discharged for the worked example. The construction
never evaluates a reciprocal expression at `d(t)=0`.

The template uses rational `1/l` and `1/u`. Its algebraic syntax is total even if
a supplied limit is zero, but soundness requires the stated bounds: if `l=0`,
those bounds make the negative guard impossible; if `u=0`, the positive guard is
impossible. There is no semantic value assigned to division by zero. For the
crossing-zero example both limits are explicitly nonzero.

`composed_encloses` propagates values through addition of `s(t)`;
`composed_domain` proves that the generated fibers are nonempty exactly when
that composed partial relation has a value. `composed_expression` connects it to
the existing `Expr.Value` for `(1/x)+y` at the original coordinates
`x=d(t), y=s(t)`. This does not turn the two coordinates into independent choices.
There is no automatic finite bound near a pole and no new default evaluator.

## Checked distinctions

[The fixture](tests/UnboundedPieceComposition.lean) uses `0 ≤ t ≤ 1`,
`d(t)=t−1/2`, and `s(t)=t`.

- The original pole remains an empty fiber. Open ray tips stay open; empty
  descriptions stay empty.
- Actual endpoint outputs are −2 and 3. Their projected closed convex hull
  contains 0, while the generated guarded pieces exclude the entire [−1,1].
- At `t=1/4`, the piece admits −7/4 but the expression cannot attain it. The
  exact representation translation is not exactness of the reciprocal enclosure.
- A represented ray has members below every finite proposed lower bound.
  `finite_tags_only` proves that encoding these real members, even followed by
  the existing tagged hull conversion, contains neither genuine ±∞ nor λ.
- Kernel-checked rational membership tests and a pure `#eval` exercise the
  compiled output pieces, not just isolated mathematical inequalities.

## Source scope

The original [thesis §2.11.4, printed pp.35–36 / PDF pp.51–52](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=52)
distinguishes a total operation retaining its inputs' domain conjunction from a
partial operation adding its own constraint. This milestone constructs that
behavior for an affine reciprocal and a subsequent total affine addition.
The visually checked [§2.13.1, printed p.39 / PDF p.55](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=55)
explicitly contrasts the good reciprocal model with two rays for `[-1,1]`
against the poor whole-hull model. The fixture instantiates the existing exact
reciprocal-image theorem for its finite real members; the displayed three-valued
flags and literal exceptional membership are not inferred from that theorem.
[SIGGRAPH 2001 §11/Figure 10(b)](https://www.dgp.toronto.edu/papers/jtupper_SIGGRAPH2001.pdf#page=6)
also motivates retaining disconnected sets.

The half-space grammar and translation
compiler are explicitly our finite model, not purported printed source syntax.
The paper's checked page has floor pseudocode and union-cover discussion, not a
reciprocal listing. No full def/cont-flag algorithm is claimed.

This closes compositional representation of these unbounded finite-output
pieces through affine translation, not arbitrary nonlinear operator closure,
exact pointwise reciprocal images, optimal demotion or uncertain-coefficient
classification. Literal exceptional inputs still use the separate tagged layer;
this theorem supplies no new operations on them. See the
[closeout program](CHAPTER2_CLOSEOUT.md) for the remaining substantial work.

Run `lake build UnboundedPieceComposition`,
`lake env lean tests/UnboundedPieceComposition.lean`, then `./check.sh`.
There are no new axioms, FP contracts, native changes or runtime performance claims.
