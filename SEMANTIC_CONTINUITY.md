# Continuity from defined arithmetic semantics

This milestone connects generalized guarded arithmetic to the existing
continuity/defined-root foundations without adding another expression language,
certificate structure, classifier, or floating-point model.

## The semantic theorem

`expr_continuousOn_of_defined` concerns the existing arithmetic-only Expr:
rational constants, x, y, addition, subtraction, multiplication, and division.
Given continuous coordinate functions x,y on a supplied set T and an actual
Value witness at every point of T, it proves relative continuity of the existing
Expr.realValue representative on T.

The proof follows the syntax. Definedness of a compound expression supplies
actual values for its children. In the division case, the Value constructor
supplies a nonzero denominator, and the existing value_eq_realValue theorem
identifies its value with the canonical real representative. Thus the proof
never treats Lean's totalized division by zero as a defined partial value.
`realValue_defined` similarly accepts the canonical value only after a semantic
existence witness has been supplied.

This implication is specific to the current arithmetic primitives. It does not
hold for arbitrary total functions, multivalued relations, or conditional trees.
A conditional jump can be defined everywhere and discontinuous. The existing
jump controls remain intact; no theorem here accepts ConditionalValue or an
arbitrary PartialEnclosure.Sound contract as a continuity premise.

## Interpreter and parameter-cell integration

`evalGuarded_continuousOn` obtains definedness from successful generalized
interpretation and applies the semantic theorem. It explicitly requires T to
lie in [0,1], coordinate enclosure at each point of T, and continuous coordinate
functions on T. The result contains both continuity and actual canonical Value
witnesses. Affine bounds alone do not make the enclosed coordinate functions
continuous.

`parameter_map_continuous` reuses the existing affine segment continuity proof.
`evalGuarded_reparam_continuous` composes continuous coordinates on one original
closed cell with its map from #26, converts enclosures by the exact containment
iff, and applies guarded continuity on the new unit parameter. The enclosure
hypotheses apply only on the original cell, not on the entire original unit
range. Degenerate cells are permitted by the same theorem.

The cell theorem uses chosen total real coordinate representatives and proves
arithmetic Value for them. It does not assert that an external partial coordinate
environment admits those coordinates at every point. If the environment has a
hole, retain that domain explicitly and apply the set-relative theorem on the
actual domain, or establish whole-cell membership separately. The domain
transport and hole-preservation results from #26 are not weakened.

## Positive and negative controls

For x=t on [0,1], consider

    (x - 1/2) / ((x - x) + 1).

Ordinary interval evaluation returns unknown because it loses cancellation in
the denominator. The generalized evaluator succeeds. The new theorem supplies
continuity and definedness; exact endpoint bounds and the existing
certified_curve_zero theorem yield an actual partial-semantic root. This is a
specific integration example, not a general precision comparison or a changed
presence classifier.

A reciprocal on the restricted cell [1/2,1] obtains a continuity certificate;
a separate semantic proof rejects a value at the excluded original coordinate
zero. No claim of global definedness is made.

For 1/(t-1/2) on the punctured set [0,1] minus {1/2}, independent Value
constructions and the semantic theorem prove relative continuity. Endpoint
values have opposite signs, yet a separate constructor proof establishes that
there is no defined zero anywhere and no value at the midpoint. This demonstrates
why relative continuity on a disconnected/punctured domain cannot be used as
continuity and definedness on the full interval required by the IVT certificate.
It also prevents a totalized value at the pole from becoming a claimed root.

## Thesis alignment and limits

Tupper [§2.12](https://www.dgp.toronto.edu/~mooncake/thesis/node52.html) discusses
recursive property tracking, and
[§3.3.18](https://www.dgp.toronto.edu/~mooncake/thesis/node124.html) treats
continuity descriptions separately from values. This is one narrow, proved
property rule for the existing rational arithmetic fragment. It is not the
thesis's full numerical continuity-description machinery.

No continuity is glued across a finite cover, and no matching-boundary or
conditional-branch rule is introduced. A supplied cover transfers pointwise
claims as in #26; it does not by itself imply global continuity. Executable
domain analysis, maximal domains, arbitrary property tracking, new primitives,
FP implementation correctness, and native application integration remain outside
scope. Prior ordinary continuity proofs and all evaluator definitions remain
unchanged. The current module imports their established realValue and segment
lemmas rather than duplicating those interfaces. Future consolidation of the
old structural proof is separate from this semantic extension.

See VALIDATION.md for kernel build, enforced axiom audits, module reachability,
and negative-control results. No additional FP assumptions or hosted CI are
introduced.

The later [closed-cell composition module](CELL_CONTINUITY.md) adds a bounded
gluing theorem for a common function on finite closed covers. The arithmetic
and relative-continuity statements in this milestone remain unchanged.
