# Finite family inclusion and constant projection

This proof-only bridge connects the existing rational endpoint affine family,
constant intervals, actual real-output fibers, extended closed hulls and the
existing supplied-word demotion certificate. It generates no bound coefficients
and runs no native code.

## Source correspondence

Tupper §2.9.3, printed pp.28–30 / PDF pp.44–46, defines inclusion at the same
parameter, distinguishes a constant interval from a parameterized linear one,
and describes outward function demotion. The original
[printed p.29 / PDF p.45](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=45)
was visually checked for the inclusion and infimum/supremum extension formulas,
pointwise demotion and the `x-x` example. The rational endpoint representation
is the existing finite specialization, already related to coefficient form in
[LinearIntervals](LinearIntervals.lean); it is not the entire extended-real
source family. The §2.10 certificate is reused from
[FiniteAffineDemotion](FiniteAffineDemotion.lean), not reimplemented.

## Exact claims

[FamilyDemotion](FamilyDemotion.lean) proves:

* `fiber_demotion_iff`: enclosing an actual real-output fiber is equivalent to
  enclosing its least extended closed hull. This includes empty/unbounded fibers
  using the existing hull conventions; it makes no claim about exceptional
  arithmetic values. `relation_demotion` keeps the same parameter, admissible
  input and partial relation witness, without assuming independent operands.
* `exact_fiber_domain`: the exact hull has a real member iff the original fiber
  does. Arbitrary outward widening need not preserve this equivalence.
* `linear_inclusion_iff`: four endpoint inequalities are necessary and sufficient
  for pointwise containment between two existing `LinearInterval` values on
  `[0,1]`. This reuses `affine_order_iff` and endpoint noncollapse; it is not a
  rule for arbitrary nonlinear bounds or parameters outside that domain.
* `constant_least` and `constant_hull_exact`: the existing `LinearInterval.hull`
  equals the generic least closed hull of all values admitted by the family
  over `[0,1]`. Its constant enclosure is least even among real closed bounds,
  not merely among rational candidates. The proof reuses existing hull soundness,
  actual attained family endpoints, and generic finite/extended hull agreement.
* `constant_embedding_exact`: embedding a constant interval preserves each fiber.
* `certified_relation`: compose an ideal affine enclosure of an actual relation
  with a successful supplied-word certificate. Every actual value retains the
  same parameter through both stages. This is conditional on the explicit ideal
  enclosure and certificate; no rounder, success or optimality is inferred.

These statements use existing representations, not a new universal family API.
No claim is made that the constant hull equals the attainable image of an
arbitrary expression. It is the least closed hull of the *admitted family range*;
a particular expression may attain fewer values. Likewise this does not prove
that an arbitrary real function has a finite affine demotion.

## Exact, lossy and inapplicable

Constant embedding is exact fiber by fiber. The constant hull is exact as a
least closed projection, but loses the association between parameter and value.
For the exact seed `x=t`, projecting to `[0,1]` admits value 1 at parameter 0,
which the original family excludes. Projecting before independent interval
subtraction admits 1, while the original shared-parameter `x-x` result is 0.
The latter reuses the existing cancellation theorem and mirrors the source.

Restricting the parameter to `{1/2}` makes the seed's actual range `{1/2}`;
the full-domain constant hull still admits 1. Consequently the leastness theorem
is for its stated full parameter domain, not any externally restricted domain.
For a restricted/partial relation use its actual fibers in `relation_demotion`.

[Kernel-checked controls](tests/FamilyDemotion.lean) additionally show:

* parameter 2 lies outside the hull-enclosure theorem's `[0,1]` premise;
* endpoint checks cannot bound `t*(1-t)` by zero in the interior;
* an empty fiber is soundly enclosed by nonempty `[0,1]`, so numeric containment
  does not establish definedness or preserve domain classification;
* no finite `QInterval` encloses all real values;
* constant embedding retains every original membership test.

Exceptional comparison behavior, extended coefficients, arbitrary polynomial/
functional/symbolic family conversions, domain descriptor synthesis and full
source promotion remain outside this result. No new FP assumptions, hardware
execution, native/Word bridge, exact rounding, ULP, performance or general
optimal-function-demotion claims are made.

## Verification and status

```sh
lake build FamilyDemotion
lake env lean tests/FamilyDemotion.lean
RELGRAPH_CHECKOUT=/path/to/pinned/relgraph ./check.sh
```

See [validation](VALIDATION.md), [completion ledger](CHAPTER2_COMPLETION.md)
and [concordance](THESIS_CONCORDANCE.md). Chapter 2 remains incomplete.
