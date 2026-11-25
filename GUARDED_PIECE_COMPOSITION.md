# Generated domains through guarded expression composition

Tupper §2.11.4 says total operations retain the conjunction of input constraints and partial operations add their own domain constraint (printed pp.35–36 / [PDF pp.51–52](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=52), visually checked). [GuardedPieceComposition.lean](GuardedPieceComposition.lean) gives a restricted constructive bridge from the [generated finite-band descriptors](PIECE_DOMAIN_CONVERSION.md) to the existing `Expr`, `Value` and `evalGuarded` machinery. It does not add an evaluator or silently define division at zero.

## Construction and theorem

`bounds?` builds the existing `LinearInterval` only when the two rational endpoint-order checks succeed on the full unit parameter interval. `evaluate?` builds both coordinate intervals, runs the unchanged guarded evaluator, and pairs a successful result with the explicit conjunction of:

- the unit-parameter constraints;
- the generated first-band feasibility/guard constraints;
- the generated second-band feasibility/guard constraints.

The guard is a finite `FiniteGuardPieces.Guard` and can be compiled and tested with the existing rational reference checker. Whole-hull division checks are performed by `evalGuarded`; success proves every admitted coordinate pair has a defined expression value. Thus the operation-domain obligation is discharged on a successful result rather than assumed from nonempty inputs. No extra symbolic nonzero constraint is needed in this **successful whole-hull-guarded** case.

For `evaluate? b c e = some r`:

- `evaluate_encloses` encloses every actual `Value x y e z` whose coordinates come from `b` and `c` at the same `t ∈ [0,1]`.
- `evaluate_domain_exact` proves that `r.domain` holds exactly when such an actual value exists.
- `admitted_exact` proves the executable rational-parameter domain test agrees with that real semantics.
- `family_classification_exact` preserves definite and possible classifications over a list of original choice indices, **using the same index for both coordinates before projection**. Every admitted choice must have a successful evaluator result; failed choices cannot be discarded to justify an exact classification.
- `family_encloses` retains that original choice for the output bound.

These are arbitrary-expression results within the existing guarded evaluator's grammar, conditional on its checked success. Both coordinates must exist even if the expression does not use one; this matches the existing strict coordinate-environment semantics, not minimal free-variable analysis. Within one supplied band pair, allowed coordinates form the Cartesian product at the same parameter; additional cross-coordinate relations are not inferred from sharing a parameter. Repeated AST occurrences still reuse one chosen pair. Values are finite real numbers. The guard and numerical field must be consumed together; an unguarded numerical field alone is not evidence that a source value occurs.

## Worked composition and failure controls

[Fixtures](tests/GuardedPieceComposition.lean) evaluate `1 / ((1+t)+1)` with `0 ≤ t < 1/2`. The actual AST reuses the pair `(1+t,1)` throughout. The generated enclosure is `[1/3,1/2]`, and the theorem encloses `1/(2+t)` at every admitted parameter. At `t=1/2`, ordinary arithmetic on the closed numeric bands produces `2/5`, but the generated guard rejects the point: the original first-band guard excludes it. This does not mean the real arithmetic expression itself is undefined there; the represented input is absent.

A separate finite family has two opposite input-guard assignments. Each coordinate projection independently supplies the value 1 at `t=1/4`, so independent re-choice allows the sum 2. No single original choice supplies both inputs, however, and both generated joint guards reject the point. This refutes an existence/exactness claim from separate witnesses; independent Cartesian enclosure may still be conservative.

The control `1/t` on the whole unit interval fails the existing denominator hull guard, even though at `t=1` it has the actual value 1. `none` therefore remains **unknown**, never nowhere-defined. Six pure Lean reference checks execute the same constructed routes and are separately backed by kernel proofs.

## Source scope and next gap

This closes the first compositional integration of generated finite input-domain descriptions with successful guarded expression evaluation. It does not synthesize nonzero guards when the old whole-hull evaluator fails, construct unbounded output pieces near a pole, or classify failed/unsupported choices as false. Numeric bounds are sound but not claimed optimal or equal to the attainable image. The [closeout matrix](CHAPTER2_CLOSEOUT.md) records the narrowed residual.

The next mathematical integration is operation-generated domain splitting when a hull guard is inconclusive, preserving every original witness and using the existing split-quotient results where suitable. Unbounded sets of finite values are not literal infinite coefficients; this milestone models neither literal infinity nor λ and adds no exceptional arithmetic row. It changes no hardware/default path, FP premise or native implementation. Validation is in [VALIDATION.md](VALIDATION.md).
