# Finite covers on restricted parameter cells

This extends the existing ParameterCell change of parameter to finite covers by
mapping the already proved LinearInterval.reparam operation over the list. No
new cell representation, subdivision policy, coverage theorem, or interpreter
is introduced. The connection follows Tupper's shared-parameter
[linear intervals (§2.9.3)](https://www.dgp.toronto.edu/~mooncake/thesis/node39.html)
and the use of [interval sets (§2.13)](https://www.dgp.toronto.edu/~mooncake/thesis/node56.html)
for multiple possible values. It is a bounded integration of existing
representations, not a full implementation of the thesis's models.

`cover_reparam_contains` proves exact equivalence of represented membership at
local parameter s and original parameter C.map s. It holds pointwise even
outside the unit interval as an affine identity; domain and soundness claims
remain restricted to the certified unit range. Component count is unchanged.
Semantic inclusion is preserved because a valid cell maps local unit parameters
into the original unit range.

`cover_reparam_domain_sound` pulls back both definite and possible predicates
using the existing pullDomain. Its actual relation is explicitly
`s in [0,1] AND R(C.map s,z)`. This handles degenerate cells without division by
cell width and preserves holes rather than treating geometric coverage as
existence evidence.

`evalConditionalCover_reparam_relational_sound` reuses the existing conditional
cover interpreter on restricted coordinate enclosures. It transports the same
partial coordinate relations and domains as the arithmetic-only bridge from
#26. Both coordinates are still required and their domain predicates are
intersected, even for unused coordinates. It does not assert that reevaluation
commutes with restricting an already evaluated cover.

The independent multivalued example has actual values t or 1-t. Its relation,
not the mere presence of two intervals, supplies this semantics and existence.
On the closed cell [2/5,3/5]:

- Restricting the two exact affine components before coalescing yields constant
  bounds [2/5,3/5].
- Coalescing first yields [0,1], which remains [0,1] after restriction.
- Both orders have the same sound pulled-back domain contract, but the coarse
  result includes 9/10 where the fine result does not. Reverse range inclusion
  is formally refuted, so these operations cannot freely be exchanged.
- The fine result supports guarded reciprocal enclosure and definite actual
  reciprocal existence; the coarse result's zero-containing hull is unknown.
- At local parameter zero there are two distinct actual values. A theorem rejects
  any single-valued representative agreeing with all actual values. In particular,
  the single-representative presence rule from #33 cannot be applied blindly.

A second control restricts a punctured actual domain to the singleton cell
{1/2}. The numerical bounds remain nonempty, but every local point has no actual
value because the pulled-back domain is absent. Shrinking the cell does not
repair the hole.

The conditional integration reevaluates the jump from #32 on [1/2,1]. The guard
certifies the false branch, yielding one component; simply restricting the old
cover retains two. The original coordinate-domain hole remains absent at local
zero, while the local interior has an actual value. Equality still selects the
false branch. No unsupported branch is discarded merely by reparameterization.

These are exact rational operations. No new FP assumptions, continuity inference,
optimal coalescing rule, automatic cell search, domain discovery, application
integration or hosted CI is added. Coalescing order matters for precision; the
examples justify that specific comparison, not a general optimality theorem.
Existing output-size limits remain output-size limits, not runtime guarantees.
