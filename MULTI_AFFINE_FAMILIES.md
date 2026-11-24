# Finite multi-parameter affine families

Tupper §2.9.6, printed pp.30–31 / PDF pp.46–47, defines bounds of the form
`p + Σ qᵢ αᵢ`, with the vector α ranging over `[0,1]^k`. The original
[PDF p.47](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=47) was visually
checked, including §2.9.7's same-vector inclusion and noncollapse definitions.
The coordinates can vary independently within a vector; different occurrences
of an input must not silently receive different vectors.

[MultiAffineFamilies.lean](MultiAffineFamilies.lean) supplies this **finite rational
coefficient** instance for every `n : Nat`, including zero. `Form.value` is its
exact real interpretation, and `Bounds` pairs two such forms. This is proof-side
mathematics, not a new native backend or an extended-coefficient implementation.

## Checked results

- `attained_lo`, `attained_hi`, `encloses`: the sign-selected cube corners attain
  `p + Σ min(0,qᵢ)` and `p + Σ max(0,qᵢ)`, and enclose every value on the cube.
- `order_iff`: pointwise order of two forms on the whole cube is equivalent to
  the rational upper extremum of their difference being nonpositive. `Bounds`
  uses this exact criterion for noncollapse. `inclusion_iff` gives two such
  checks for pointwise inclusion between interval families.
- `add_value`, `sub_value`, `scale_value`: coefficient operations agree exactly
  with real affine addition, subtraction and rational scaling at the same vector.
  These are form operations, not an asserted complete interval evaluator.
- `hull_endpoints_attained`, `hull_least`, `hull_exact`: the lower bound's minimum
  and upper bound's maximum are admitted at their respective corner vectors;
  the resulting rational interval is the least closed real hull of the actual
  union of fibers, agreeing with `ExtendedImageHull`. This does not assert that
  every interval-admitted value occurs in a separately modeled expression.
- `constant_demotion`: that projection instantiates the existing family demotion
  contract, preserving the cube domain. Existing `sound_demote` and
  `restrict_sound` retain the actual witness and any supplied external holes.
- `fromQAffine_value`, `fromLinear_contains`, `fromLinear_equality`: exact
  correspondence with the existing one-parameter endpoint representation.
  No one-dimensional canonical-or-full-endpoint theorem is generalized to a
  cube by silently inspecting only two diagonal vertices.

## Controls and limits

[Fixtures](tests/MultiAffineFamilies.lean) check a two-parameter form
`2 + 3α − 5β` with attained extrema −3 and 5, negative scaling, and zero parameters.
For `α−β`, both diagonal vertices (0,0) and (1,1) give zero, while (0,1) gives −1:
two-endpoint checking would miss collapse. The exact order criterion rejects it.
The same vector gives `f−f=0`; independent vectors spuriously give 2. Restricting
to α=β also gives zero, so full-cube extremality must not be claimed on an
arbitrary restricted domain. Constant projection can lose individual fibers.

The rational extremum/order formulas are exact mathematical criteria; this
milestone supplies proof-side/noncomputable definitions, not an executable
checker or native performance/machine-rounding claim. The definitions avoid
compiler-generated closure artifacts being treated as logical roots by the
unchanged audit; every theorem's actual dependencies remain audited. Extracting
an executable checker is separate future work, not required for these theorems.

Moved to checked: finite rational §2.9.6 representation, exact pointwise
noncollapse/inclusion, affine operation correspondence, attained extremal hull
and its general-family projection instance. Still open: extended/undefined
coefficients, the full real-coefficient carrier, quadratic family correspondence,
general nonlinear operator demotion, and native family realization. §2.9.7's
arbitrary functional/symbolic coefficient language is not constructed here.
The independent §2.9.3 source interpretation remains unchanged.

Run the pinned `./check.sh`; module, fixture and named audits are registered.
This belongs to the families, sets and demotion review unit.
