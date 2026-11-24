# Finite-arity strict composition and sufficient property transport

[FiniteProperties](FiniteProperties.lean) extends the existing unary partial-real
core to a tuple indexed by `Fin n`. It is a mathematical, noncomputable denotation:
there is no runtime evaluator, evaluation-order claim or new syntax/backend.

## Exact definedness

`collect_some` proves that the collected tuple is exactly v iff every child
returns `some (v i)` at the same input x. Although the definition uses classical
choice, this theorem identifies the tuple uniquely through actual child results.
`composeN_some` proves:

```
composeN g f x = some z ↔
  ∃ v, (∀ i, f i x = some (v i)) ∧ g v = some z
```

`composeN_defined` existentially quantifies z. This is all children defined AND
the outer operation defined on their shared tuple, not independent marginal
witnesses. `missing_input` proves absence propagates even when an outer formula
would ignore that input. Nullary defined and undefined operators are both tested.
Strictness is explicit; this is not lazy conditional evaluation.

## Sufficient continuity and local constancy

`continuous_composeN` requires each actual partial child to have a continuous
real representative on S, the outer partial operation to have one on T, and
every actual tuple from S to lie in T. The result is continuously defined on S
in the existing `ContinuousOnPartial` sense. Product topology and mathlib's
composition theorem provide the proof. No reverse implication is claimed.

`LocallyConstantWithin f S x` requires an actual value at x and the same value
throughout some relative neighborhood within S. `locally_constant_composeN`
uses finitely many such child neighborhoods to obtain one common neighborhood,
and requires the outer operation to be defined on their fixed tuple. It need
not be continuous elsewhere. The explicit value-at-x premise prevents an empty
relative neighborhood from manufacturing a value. This is a sufficient
all-children-constant case, not the source's full selective child-flag rule.

The existing [semantic continuity theorem](SemanticContinuity.lean) already
proves recursive continuity for the arithmetic `Expr` language when coordinates
are continuous and actual values exist throughout the set. We reuse it rather
than add a second AST. `expr_locally_fixed` adds the matching recursive semantic
corollary: locally fixed coordinates preserve an existing `Expr.Value` witness,
including every division guard. It does not create a value when that witness is
absent, nor handle syntax outside the existing Expr language.

## Source scope and controls

Tupper §2.12 printed pp.36–37 / PDF pp.52–53 introduces an m-ary tuple of inner
functions and recursive property checks. The original pages were visually
verified in the [unary milestone](PARTIAL_PROPERTIES.md). These theorems implement
the sound strict-definedness core and sufficient property transport under stated
domains. The printed weak-continuity direction remains obstructed by the existing
[checked counterexample](tests/PropertyComposition.lean); this does not silently
reverse it or claim semantic equivalence of recursive flags.

[Fixtures](tests/FiniteProperties.lean) check two genuine varying inputs with a
continuous outer addition, an absent ignored input, both nullary cases, finite
local-constant composition, an empty-relative-set failure, shared-input
cancellation and the actual Expr corollary. Shared witnesses remain distinct
from independent interval projections.

No new FP assumptions, hardware/default changes, expression-value totalization,
local-constancy equivalence or completed Chapter 2 claim is introduced. The selective-flag sufficient rule is documented in [tracking](TRACKING_CERTIFICATES.md);
full source equivalence, generic recursive syntax and property descriptor
construction remain unproved.

```sh
lake build FiniteProperties
lake env lean tests/FiniteProperties.lean
RELGRAPH_CHECKOUT=/path/to/pinned/relgraph ./check.sh
```

See [validation](VALIDATION.md), [ledger](CHAPTER2_COMPLETION.md),
[concordance](THESIS_CONCORDANCE.md).
