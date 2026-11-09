# Piecewise selection, domains, and discontinuity

`PiecewiseSelection.lean` adds a bounded compositional selection operator for
partial branch relations. The branch predicate is a **total predicate of the
shared parameter**. This milestone does not assign values to undefined guards,
add conditionals to `Expr`, or implement lazy evaluation of failing branch code.

## Decisions and value bounds

`BranchDecision` has `yes`, `no`, and `unknown`. `BranchSound` requires a yes/no
claim to hold throughout `[0,1]`; unknown makes no truth claim.
`decideLinearLt G q` is an executable rational classifier for a strict comparison:

- hull upper endpoint `< q` certifies yes;
- `q ≤` hull lower endpoint certifies no;
- otherwise the decision is unknown.

`decideLinearLt_sound` proves this classifier correct for a supplied total real
guard function enclosed by `G` throughout the parameter range. Equality belongs
to the false branch. A box whose upper endpoint equals the threshold can still
be unknown, because some points may satisfy the strict comparison. Unknown does
not imply that both truth values occur or that the guard is undefined.

For branch value bounds `I,J` and domain descriptions `D,E`, selection uses:

| Decision | Value bounds | Definite domain | Possible domain |
| --- | --- | --- | --- |
| yes | I | D.definite | D.possible |
| no | J | E.definite | E.possible |
| unknown | I.join J | D.definite ∧ E.definite | D.possible ∨ E.possible |

The usual `onDomain` wrapper additionally restricts parameters to `[0,1]`.
`PiecewiseValues P A B t z` requires a value from A when `P t`, or from B when
`¬ P t`. The inactive branch need not have a semantic value.

`select_domain_sound` proves all three output contract clauses: enclosure of
actual values, possible domain membership of actual values, and existence from
definite membership. A known choice retains only the active domain. An unknown
choice requires both branches to be definitely defined before guaranteeing
existence, but preserves either branch as a possible source. These bounds can be
conservative: they do not infer maximal piecewise domains from pointwise guards.

## Compositional integration and its limits

`select_guarded_branches_sound` combines two successful `evalGuarded` branch
interpretations with a sound branch decision. It is an external selection
combinator with a proved semantic contract, not a new conditional AST or a
runtime promise to skip evaluating the inactive branch. This bridge requires
both interpretations to succeed. The more general `select_domain_sound` can
handle an undefined branch described by an empty semantic relation and a sound
empty-domain contract; that is how the inactive-undefined-branch control works.

This selection semantics does not alter the strict complete-coordinate
environment used inside each interpreted branch. Nor does it encode arbitrary
joint coordinate constraints or infer definedness of partial guard expressions.
No floating-point assumption is added; value and comparison computations use
exact rational coefficients interpreted over reals.

## Discontinuity is not silently discarded

The checked jump example uses predicate `t < 1/2` with values -1 and 1. Both
branches are total on `[0,1]`, and the decision is unknown across that range.
The selection is enclosed by `[-1,1]`. Independent proofs establish its opposite
endpoint values and absence of any zero. A further theorem proves that the jump
is **not continuous on `[0,1]`**, using the existing intermediate-value theorem
only as a contradiction argument. Thus the value/domain result cannot serve as
a continuity or root-presence certificate.

Other controls check strict-comparison boundaries, existence with an undefined
inactive branch, absence when that undefined branch is active, possible-but-not-
definite information for an unresolved partial selection, and the bridge from
actual guarded interpreter outputs. These are kernel-checked mathematical
controls; the audit enforces the existing axiom allowlist.

## Thesis connection

Tupper [§2.9.2, Three Valued Logic](https://www.dgp.toronto.edu/~mooncake/thesis/node38.html)
treats the unknown value as lack of knowledge. [§2.12, Property Tracking](https://www.dgp.toronto.edu/~mooncake/thesis/node52.html)
distinguishes additional properties from value information, and
[§3.3.18, Discontinuous Functions](https://www.dgp.toronto.edu/~mooncake/thesis/node124.html)
tracks a continuity description separately from values. The operator here is a
small semantic specialization consistent with those distinctions, not a proof
of the full thesis logic isomorphism, property-propagation system, or conditional
optimization algorithms. It deliberately returns no continuity certificate.

See [VALIDATION.md](VALIDATION.md) for build/audit counts and
[REVIEW_STACK.md](REVIEW_STACK.md) for the incremental review. No old interpreter,
presence proof, native build/release, dependency pin, or hosted CI is changed.

The subsequent [conditional-tree milestone](CONDITIONAL_EVALUATOR.md) adds a
separate syntax with partial arithmetic guards and certified inactive-branch
independence. It does not change this external selection contract or its
two-success interpreter composition premise.
