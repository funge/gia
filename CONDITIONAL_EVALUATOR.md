# Conditional trees with active-branch semantics

`ConditionalEvaluator.lean` adds a finite conditional tree wrapper around the
existing arithmetic language. A tree is either an arithmetic leaf or
`iteLt guard q yesBranch noBranch`, where `guard` is an existing `Expr`, `q` is
rational, and both branches are conditional trees. Nested branch conditionals
are supported. Conditional nodes inside arithmetic operations or guard
expressions are not added in this bounded grammar; the old `Expr` is unchanged.

## Partial guards and active branches

`ConditionalValue x y e z` is the new partial real semantics. A conditional value
requires an actual `Value x y guard u`. It then requires a value only from the
true branch if `u < q`, or only from the false branch if `q ≤ u`. Equality selects
the false branch. The inactive branch has no value premise. All guard and branch
evaluation uses the same chosen coordinates, preserving their semantic
relationship through the tree.

An undefined guard cannot be silently treated as false, even if both branches
are identical constants. Conversely, an undefined inactive branch does not
invalidate a defined guard and active branch.

This differs deliberately from #22's external selection interface, which takes
a total predicate and a global `BranchSound` certificate. Here guards are partial
arithmetic expressions; their definedness is proved locally using the existing
guarded interpreter. No total real guard function or global predicate certificate
is assumed. #22's existing operator and two-success composition theorem remain
unchanged.

## Evaluation policy and proved claims

`evalConditional` first interprets the arithmetic guard. If this fails, the
result is `none`. For a successful guard enclosure:

- a certified true decision recurses only into the true branch;
- a certified false decision recurses only into the false branch;
- an unknown decision requires both branch enclosures and joins them; failure
  of either required branch returns `none`.

`evalConditional_known_yes` and `evalConditional_known_no` prove exact equality
with the selected branch evaluation, independently of the inactive tree. This
is non-strict branch evaluation at the Lean definition/semantic level, not a
native-code cost model or a verification of compiler execution behavior.

`evalConditional_sound` proves enclosure for every semantic value at a certified
parameter and enclosed coordinates. `evalConditional_defined` proves an actual
conditional value from success under those same local premises. For an unknown
decision, it constructs the guard value, determines its actual comparison in the
proof, and supplies the appropriate branch witness. It does not assume that a
guard enclosure implies a guard value.

`evalConditional_relational_sound` carries all three partial-coordinate contract
obligations into the conditional tree. The existing strict complete-coordinate
environment is retained: both coordinate bindings must exist, even if unused.
Separate unary coordinate relations are not an arbitrary joint-domain analysis.
Leaf evaluation is definitionally the existing guarded interpreter, and a proved
iff identifies leaf semantics exactly with the old `Value` relation.

## Meaningful controls

`ConditionalExamples.lean` uses actual division-by-zero syntax, not merely an
abstract empty branch relation. Kernel computations and separate semantic proofs
check certified true/false choices that skip poles, active poles, equality,
nested choices skipping an undefined guard, and an undefined guard with identical
branches. Undefined guards and active poles are separately proved to have no
semantic value.

A reciprocal guard succeeds on the certified input range but the resulting tree
is proved undefined at an out-of-range coordinate where that guard has a pole.
This protects against an unrestricted/global definedness claim. An unresolved
partial tree returns unknown while having a directly constructed value at one
point and no value at another. An unresolved total jump receives joined bounds
and is related to the previously proved discontinuous jump; no continuity or
root certificate is inferred. A punctured coordinate environment retains its
excluded parameter despite successful branch selection.

## Thesis relation and limits

The distinction between value and domain information follows the earlier
formalization of Tupper [§2.11](https://www.dgp.toronto.edu/~mooncake/thesis/node46.html)
and [§3.3.16](https://www.dgp.toronto.edu/~mooncake/thesis/node122.html).
[§4.1.4, Syntax](https://www.dgp.toronto.edu/~mooncake/thesis/node148.html) discusses
building richer syntax from basic operators and the effect of representations
on interval bounds. [§4.5, Removing Conditionals](https://www.dgp.toronto.edu/~mooncake/thesis/node166.html)
uses previously certified operator cases to specialize further evaluation.
Our exact inactive-branch independence proofs are a bounded semantic step toward
such specialization, not an implementation of the thesis's caching, generated
operator rules, or rounding-control optimizations.

Unknown remains possible for trees whose active branch is defined throughout an
intended restricted domain: domain predicates do not narrow the numerical guard
or split its parameter range. There is no maximal-domain, continuity, completeness,
optimality, or machine-correctness theorem. No FP assumptions, native build/release
requirements, hosted CI, or dependency pins change. See [VALIDATION.md](VALIDATION.md)
and [REVIEW_STACK.md](REVIEW_STACK.md) for evidence and review scope.

The subsequent [arithmetic composition](CONDITIONAL_ARITHMETIC.md) module adds
proved operations on these trees without changing this grammar or evaluator.
Its transformed trees can represent conditional operands inside arithmetic.
