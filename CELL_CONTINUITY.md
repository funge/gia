# Continuity composition over finite closed covers

This milestone builds on #26's ParameterCell/ParameterCover and #27's local
arithmetic continuity. It adds three general theorems, without another cell
representation, subdivision policy, or property-certificate data type.

## Recovering continuity on the original cell

`parameter_cell_continuous_iff C g` proves equivalence between continuity of g
on C's original closed interval and continuity of g composed with C.map on
[0,1]. The forward direction reuses parameter_map_continuous. The reverse
uses the continuous affine inverse on a positive-width cell. A zero-width cell
is handled as a singleton, without division by a zero width.

This is a topological equivalence for the same supplied real function. Exact
bound containment remains governed by #26; continuity is not inferred from
bounds or from domain membership alone.

## Finite-cover composition and agreement

`parameter_cover_continuous` accepts the existing proved ParameterCover and
continuity of g composed with each cell map. It recovers continuity on each
original closed cell and combines them with mathlib's finite closed-set union
continuity theorem. Coverage then gives continuity on the original unit range.
The finite list may overlap and contain duplicates or point cells. No infinite
closed-cover theorem is asserted.

There is one common g. Each local continuity claim includes both endpoints of
its closed cell. It is not enough to show that separately selected branch
functions happen to be continuous away from the shared boundary.

`parameter_cover_continuous_of_agreement` makes this side condition explicit
for supplied local functions f(C,s): each must be continuous on the unit range
and equal g(C.map(s)) at every local parameter, including all overlaps and
endpoints. This is stronger than checking only endpoint equality when cells
overlap over an interval. The theorem does not construct g, infer agreement,
or choose a branch at the boundary.

## Continuity and definedness remain separate

The continuity theorems concern a total real representative g. They do not
claim membership in a partial-value relation. To use an IVT result as an actual
partial-semantic root, local value witnesses must also be transferred through
the cover. A geometric cover cannot fill a semantic domain hole. In particular,
continuity on a punctured set is not the whole-cell premise here.

The positive example proves both obligations separately for the same expression:

    (x - 1/2) / (x*x + 1/8),  x=t on [0,1].

The existing whole-range guarded linear evaluation is unknown, because its
lower bound for x*x makes the denominator guard inconclusive. Reparameterized
evaluation succeeds on each closed half. #27 supplies local continuity and
actual Value witnesses; the new theorem glues continuity, while #26's cover
pullback transfers the Value witnesses. Existing endpoint bounds and
certified_curve_zero then produce an actual defined root. Neither an evaluator
nor a graph classifier is replaced, and no general precision comparison is
claimed.

## Boundary and hole controls

- Both half-cell certificates include the midpoint, and their canonical values
  there are proved equal.
- The constants -1 and 1 are separately continuous. Nevertheless, no common g
  can agree with -1 on the entire closed left cell and with 1 on the entire
  closed right cell: their shared midpoint would have conflicting values.
- Two closed cells leaving the midpoint uncovered are proved not to satisfy
  ParameterCover. Geometric coverage is a required proof, not a heuristic.
- A point cell admits a continuity certificate for any g after constant
  reparameterization; this says nothing about points outside that cell.
- The reciprocal pole from #27 cannot supply Value certificates on the complete
  two-half cover, because the midpoint is included and has no semantic value.
  This reuses the existing undefinedness proof rather than redefining poles.

## Thesis relation and limits

The work is a bounded composition rule supporting the distinction between
values, domains, and recursively tracked properties in Tupper
[§2.12](https://www.dgp.toronto.edu/~mooncake/thesis/node52.html) and the separate
continuity descriptions in
[§3.3.18](https://www.dgp.toronto.edu/~mooncake/thesis/node124.html). The actual
gluing argument uses mathlib's closed-set topology; it is not a transcription
of the thesis's numerical continuity-description encoding.

Local certificates and agreement are supplied proofs. This does not add an
automatic conditional continuity analyzer, branch matching, adaptive cover
construction, maximal-domain inference, new FP assumptions, or a complete
property-tracking framework. Discontinuous jumps and missing-domain points
remain excluded by explicit hypotheses and negative controls. Native build,
release workflow, existing mathematical interfaces, and hosted CI are unchanged.
See VALIDATION.md for the full local validation results.

The subsequent [conditional rule](CONDITIONAL_CONTINUITY.md) uses this gluing
foundation and supplies a dedicated positive regression for distinct local
representatives on overlapping cells, as requested during the #28 review.
