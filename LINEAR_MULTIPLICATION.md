# Multiplication with a shared parameter

`LinearMultiplication.lean` extends rational linear intervals with a sound
multiplication operation. It retains dependence on the common parameter
`t ∈ [0,1]`, uses exact rational coefficient arithmetic, and adds no floating-point
assumption. The old expression evaluator and graph classifiers are unchanged.

## Enclosure policy

For affine functions `a` and `b`, write `a₀,a₁,b₀,b₁` for endpoint values and set
`q = (a₁-a₀)(b₁-b₀)`. Their product has the exact identity

```
a(t)b(t) = (1-t)a₀b₀ + t a₁b₁ - q t(1-t).
```

`affine_product_identity` proves this identity; `parameter_bubble_bounds`
proves `0 ≤ t(1-t) ≤ 1/4`. Consequently the endpoint chord shifted downward by
`max(q,0)/4` is a lower bound, and shifted downward by `min(q,0)/4` is an upper
bound. `QAffine.productBounds` implements these rational affine bounds, and
`affine_product_encloses` proves inclusion. The correction is essential: the
endpoint chord alone is not generally an enclosure.

For two uncertain linear intervals, all four products of lower/upper affine
bounds are enclosed this way. `LinearInterval.join` combines their bounds using
endpoint minima and maxima. The join's affine bounds contain each input at every
parameter in `[0,1]`. `real_product_bounds` proves the ordinary four-corner
product property over reals without sign assumptions. `linear_mul_encloses`
combines these results to enclose every product of operand values at the **same**
parameter. Equal uncertain descriptions do not imply that their actual values
are equal; the examples explicitly retain negative cross-products in that case.

The result is a linear enclosure, not an exact representation of a general
quadratic. It retains some dependence but can lose information through the
curvature correction and joins. It is not claimed to be optimal, inclusion-
monotone as an operation on representations, or uniformly tighter than ordinary
interval multiplication. For example, the chosen enclosure of `t²` is
`[t-1/4,t]`, whose ordinary hull includes a negative lower bound. In contrast,
`t(1-t)` has hull `[0,1/4]`, tighter than `[0,1]` obtained by first forgetting
parameter dependence. Constant-factor controls have zero curvature correction.

## Domain preservation

`DomainBounds.inter` intersects both definite and possible domain descriptions.
`LinearInterval.onDomain` attaches a supplied description to linear value bounds
and restricts both descriptions to the certified parameter range `[0,1]`.
It does not assume that all parameters are definitely defined.

`linear_mul_domain_sound` takes sound partial operand relations and proves the
product relation sound under the intersected domain. This proves range enclosure,
possible definedness of every product value, and existence at definitely defined
parameters. No continuity or uniqueness premise is introduced.

A control multiplies zero by a constant-one relation that is undefined at zero.
The product value bounds are zero, but the product remains undefined at zero;
existence is proved at parameter `1/2`. Thus algebraic simplification of values
cannot silently discard the domain obligation. Unknown domain information stays
subject to the existing semantic contract; there is no new executable domain
analyser, status decision procedure, or division implementation.

## Relation to Tupper

[§3.3.1, Interpolating Polynomials](https://www.dgp.toronto.edu/~mooncake/thesis/node107.html)
describes constructing linear bounds using polynomial interpolation and
concavity information. [§3.3.22, Binary Functions: Two-Step Method](https://www.dgp.toronto.edu/~mooncake/thesis/node128.html)
reduces a binary bound to a function of the shared parameter before bounding it
linearly. [§3.3.25, Binary Functions: One-Step Method](https://www.dgp.toronto.edu/~mooncake/thesis/node131.html)
also considers the binary operation directly as a unary function of that
parameter. Our exact quadratic identity is a bounded specialization of this
approach to multiplication. The uniform `1/4` correction and endpoint joins are
our explicitly specified policy; this is not a proof that we reproduce all the
thesis's construction, partitioning, optimization, or optimality results.

`MultiplicationExamples.lean` checks sloping square bounds, complementary slopes,
constant-factor exactness, sign-crossing uncertain intervals, and partial-domain
preservation. See [VALIDATION.md](VALIDATION.md) for the build and axiom audit and
[REVIEW_STACK.md](REVIEW_STACK.md) for the incremental review order.
