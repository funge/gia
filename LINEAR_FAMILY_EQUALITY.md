# Shared-parameter linear families: equality and representation

Source: Tupper thesis §2.9.3, printed pp.28–30, especially
[printed p.29 / PDF p.45](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=45).
The original PDF was visually checked. Its parameter is shared, and inclusion
of an operation is stated at each parameter, not over independent marginals.
This module is the finite rational endpoint-basis specialization only.

The direct family bridge was already proved: `GeneralFamilyDemotion.affine_to_constant`
and `affine_constant_sound` preserve the domain and actual admitted witness while
reusing `linear_hull_encloses`. `FamilyDemotion.linear_inclusion_iff` characterizes
pointwise inclusion by four endpoint comparisons. We reuse those results.

[LinearFamilyEquality.lean](LinearFamilyEquality.lean) adds:

- `fibers_equal_iff`: equality of every fiber on [0,1] is equivalent to equality
  of all four endpoint coefficients.
- `hull_fibers_equal_iff`: the sound constant-hull demotion preserves every fiber
  exactly iff both bounds are constant. Equality of the overall range alone is
  insufficient. This iff uses the full parameter interval [0,1]; restricting
  the external domain may hide differences and does not imply equal coefficients.
  This is equality of represented sets, not an assertion that
  every admitted enclosure value is attained by the modeled expression.
- `exact_representative_iff`: an exact affine representative with endpoints a,b
  is contained pointwise iff a and b belong to the corresponding endpoint fibers.
  This is a necessary and sufficient condition, not an assumed demotion contract.

## A source assertion needs a specified meaning of containment

Printed p.29 says every valid linear representative of [a,b] must contain the
forward or reverse exact affine representative unless it represents a larger
domain. Under **same-parameter containment**, this is false even for finite
rational coefficients. The checked example is

`I(t) = [t/4, 1-t/4]`, for `0 ≤ t ≤ 1`.

Its actual union of fibers is exactly [0,1]: the fiber at zero covers that set,
and all other fibers stay inside it. At t=1 it admits neither 1 nor 0, so it
contains neither the forward representative t nor the reverse representative
1−t pointwise. There is no larger represented range. `shrinking_range`,
`shrinking_not_forward` and `shrinking_not_reverse` prove these facts.

The endpoint criterion above is a corrected conditional result. We do not claim
it was the author's intended correction. If “contain” means only inclusion of
total represented ranges, the example is no contradiction, but that reading
forgets the parameter and cannot supply pointwise inclusion. These two readings
must not be conflated. The source's displayed operation inclusion formula is
explicitly parameterwise; its prose assertion does not supply extra endpoint
coverage premises.

[Fixtures](tests/LinearFamilyEquality.lean) check the existing family bridge,
constant-fiber equality, strict interior fiber loss, and the combined source
counterexample. No new floating-point assumptions, coefficient rounding,
exceptional bounds, native implementation, or arbitrary-parameter family
representation are added. Run `./check.sh` with the pinned toolchain; the module
and fixtures participate in the existing axiom allowlist gate.

## Corrected canonical-or-full-endpoint alternative

`canonical_or_full_endpoint` supplies the missing alternative without choosing
an interpretation of the author's prose. For every ordered finite `LinearInterval`,
with `a = I.hull.lo`, `b = I.hull.hi`, at least one holds:

1. the exact forward representative from a to b is contained at every parameter;
2. the exact reverse representative from b to a is contained at every parameter;
3. the fiber at parameter zero is the whole hull;
4. the fiber at parameter one is the whole hull.

The lower affine minimum and upper affine maximum each occur at an endpoint.
Opposite endpoints give an orientation; the same endpoint gives a full fiber.
These alternatives are not mutually exclusive, and singleton ranges are allowed.
The proof uses existing ordered endpoints and `exact_representative_iff`.

`hull_endpoints_of_range` proves that an **exact** projected range [a,b] identifies
those hull endpoints. `canonical_or_full_fiber_of_range` then states the corrected
alternative directly with real fiber membership and the supplied rational a,b.
This equality premise cannot be replaced by a conservative range enclosure:
the constant singleton 1/2 is enclosed by [0,1] but has neither of its extrema.

The shrinking example satisfies alternative 3, while the reversed shrinking band
satisfies alternative 4. Fixtures also check that the two orientations cannot be
silently swapped, and cover a degenerate singleton. This closes a precise finite
source-family claim while retaining the original pointwise counterexample.
It neither proves the unqualified printed assertion nor constructs full
extended-coefficient or multi-parameter representations. No claim about which
alternative an algorithm will select, optimal rounding, or expression-value
attainment is made.
