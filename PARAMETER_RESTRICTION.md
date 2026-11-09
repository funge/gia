# Parameter restriction and closed coverage

`ParameterRestriction.lean` implements the bounded foundation recommended by
the integration assessment. It changes the parameterization of existing linear
coordinate models and transports their actual partial relations. No new
subdivision strategy, expression syntax, or floating-point assumptions are added.

## Exact numerical restriction

A ParameterCell contains a rational closed interval [a,b] with 0 ≤ a ≤ b ≤ 1.
Its semantic map is t = (1-s)a + sb for local parameter s in [0,1]. The map stays
in the cell and in the original unit range. `parameter_map_onto` proves that
every point of the closed cell has such a local parameter; the proof treats
a=b separately, without dividing by a zero width.

`QAffine.reparam` computes the original affine bound at rational a and b as its
new rational endpoint coefficients. `affine_reparam_value` proves exact function
composition. `LinearInterval.reparam` preserves endpoint ordering, and
`linear_reparam_contains` proves an iff between local containment and original
containment at the mapped parameter. This is exact reparameterization of the
bounds; it is not a claim that the bounds equal the underlying function.

Only coefficients are executable rational data. Real map interpretation and
domain predicates belong to the noncomputable semantic layer. The containment
identity is algebraically valid for all real s, but ordering and evaluator
certificates continue to use the unit-range premise.

## Domains are transported, not filled in

`ParameterCell.pullDomain` precomposes both definite and possible predicates
with the same map. `onDomain` supplies the local unit restriction.
`linear_reparam_domain_sound` proves enclosure, possible membership, and
existence from definite membership for

    local(s,z) := s ∈ [0,1] ∧ original(map(s),z).

`evalGuarded_reparam_relational_sound` applies the existing guarded evaluator to
the numerically restricted coordinate models and transports the two coordinate
relations/domains. Its output describes actual expression values at the original
mapped coordinates. Both coordinate bindings remain required; no joint-domain or
minimal-free-variable semantics is silently substituted.

A supplied parameter domain is not used to alter the numerical cell or to assert
that every point of that cell is defined. In particular, successful arithmetic
on a cell does not fill a hole in the coordinate environment. Failed arithmetic
continues to return unknown, including cells that touch a denominator pole.

## Coverage and shared boundaries

ParameterCover is a proposition about a supplied finite list of cells covering
[0,1]. `parameter_cover_pullback` combines coverage with surjectivity to obtain a
local representative for every original parameter. `parameter_cover_transfer`
then transports any universal claim about actual semantic values from every
cell back to the original range. The coverage hypothesis must be proved; no
coverage checker or inferred cover is introduced.

The examples construct the two halves using existing QInterval.lowerHalf and
upperHalf, prove coverage by `split_cover`, and retain their common midpoint via
`split_boundary`. These are reused from Subdivision, not duplicated. The new
core module does not import graph search/subdivision; only the example module
uses that existing construction. Overlapping endpoints are allowed, not assigned
arbitrarily to one branch. No continuity, presence, or existence claim follows
from coverage alone.

## End-to-end controls

- For x=t, `1/x` is unknown on [0,1], succeeds with [1,2] on [1/2,1], and stays
  unknown on [0,1/2]. The point cell {1/2} evaluates to exactly 2.
- Successful right-cell interpretation is connected to local Value existence.
  With a supplied coordinate-domain hole at t=1/2, the relational interpretation
  excludes the right endpoint s=0 despite numerical success, and supplies an
  actual interior value at s=1/2. The same boundary remains excluded at s=1 in
  the left cell. The degenerate cell over the hole has no possible domain at any
  local parameter, despite its numerically successful reciprocal calculation.
- The strict guard t<1/2 remains unknown on the closed left cell because it
  includes equality; it is certified false on the right. Restriction alone is
  not a strict-boundary decision procedure.
- Interpretation of x+2 on restricted coordinate models proves positivity of
  every actual value locally. The finite coverage theorem transfers this claim
  back to every original parameter, including the shared midpoint.

## Thesis relation and remaining limits

Tupper's [§2.9.6](https://www.dgp.toronto.edu/~mooncake/thesis/node42.html)
discusses maps from actual parameters to system parameters. This implementation
makes one elementary affine change of parameter explicit and proves its laws;
it does not add multiple independent parameters.
[§2.11](https://www.dgp.toronto.edu/~mooncake/thesis/node46.html) distinguishes
value and domain information. Pulling both through the same map respects that
separation, without claiming its numerical domain-description machinery.

The API accepts closed rational cells inside the original unit interval. It
has no automatic cell selection, adaptive search, open-endpoint representation,
finite interval-set evaluator, correlation pruning, maximal-domain inference,
continuity-property propagation, or optimality claim. It does not claim that
re-evaluating a restricted model commutes with restricting a previously computed
nonlinear result. Each cell's evaluator certificate is proved separately.
Existing FP assumptions and the native release/build remain unchanged.

See VALIDATION.md for full build, module coverage, negative audit controls, and
axiom evidence. The earlier integration assessment remains a historical
snapshot; this module addresses only its bounded restriction/coverage proposal.
