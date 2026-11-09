# Conditional covers with domain semantics

This milestone connects finite unions of linear enclosures to the existing
conditional interpreter and its partial coordinate environments. It introduces
no new expression syntax. The scalar interpreter remains available unchanged.

Tupper's [interval sets (§2.13)](https://www.dgp.toronto.edu/~mooncake/thesis/node56.html)
retain separated ranges; his [interval function domains (§2.11)](https://www.dgp.toronto.edu/~mooncake/thesis/node46.html)
describe whether values exist. The implementation keeps those roles distinct,
using the existing relational semantics and definite/possible domain predicates.
It does not claim to implement every thesis representation or analysis.

`evalConditionalCover` uses the same arithmetic guard evaluation and certified
comparisons as `evalConditional`. A leaf returns a singleton cover. A known
choice evaluates only the selected branch. An unknown choice requires both
branches and appends their covers rather than joining their ranges. Failed
guards or required branches return `none`, which means unknown. There is no
failure-to-empty conversion or removal of unsupported branches.

`evalConditionalCover_success` proves exact equality of success flags with the
scalar interpreter, for every input interval and conditional tree. The new
interpreter therefore changes range precision, not which trees it accepts.
`evalConditionalCover_sound` encloses every actual `ConditionalValue` at a unit
parameter with enclosed coordinates. Definedness follows from the proved
success correspondence and the existing scalar definedness theorem. Neither
result asserts global definedness outside the certified input enclosures.

`FiniteLinearCover.SoundOn D R` packages the three existing semantic obligations
for finite ranges: every actual value is enclosed, actual values imply unit
parameter membership and possible domain membership, and unit parameters in
the definite domain have actual values. This reuses `DomainBounds`; it does not
introduce another domain language. Unlike bare `Covers`, it explicitly carries
existence evidence. `cover_soundOn_covers` forgets that extra evidence when only
range exclusion is needed.

`evalConditionalCover_relational_sound` lifts the interpreter to partial
coordinate relations. As before, both coordinates are required, including
unused ones, and their domains are intersected. The result is not a minimal
expression domain and does not infer correlation between separate coordinate
relations or repeated conditional guards.

`cover_recip_domain_sound` preserves the same definite and possible domain
bounds when all components pass the existing reciprocal guard. For definite
domain points it obtains an actual input value, locates an enclosing component,
and proves that value nonzero before constructing its reciprocal. No totalized
division or nonempty-list existence inference is used.

The end-to-end regression interprets a jump between -1 and 1 with a punctured
coordinate environment. The cover excludes zero and reciprocates, whereas the
scalar joined result cannot pass the reciprocal guard. The output domain hole
at 1/2 is preserved; actual reciprocal values exist at 1/4 and 3/4. Separately,
the expression is shown defined at the excluded coordinate parameter, making
the distinction between expression and environment definedness explicit.
Known-true and equality-false cases skip inactive poles; unresolved poles and
undefined guards stay unknown. An unresolved tree still has a defined point,
and a defined zero leaf still fails the reciprocal guard. Thus unknown is not
used as a synonym for undefined. The interpreted jump remains discontinuous.

This is an exact rational implementation. No FP assumptions, continuity
inference, general cover arithmetic, normalization, resource budget, or
maximal-domain discovery is added. Covers can grow with the number of retained
leaves; no performance bound is certified here. The existing arithmetic-tree
construction may itself duplicate subtrees. A later optimization should state
and verify its resource policy rather than silently dropping alternatives.

## Threshold-local branch certificates

ThresholdCertification bridges successful branch-local evaluation to existing
ConditionalValue semantics. `evalThresholdBranches X Y q hq a b` evaluates a on
the closed cell [0,q] and b on [q,1], reusing ParameterCell reparameterization
and evalConditionalCover. The rational threshold must lie in [0,1]; degenerate
endpoint cells are supported. Success returns a pair of covers, each in its own
local unit parameter. Failure of either required branch returns none (unknown).
This does not alter the existing conditional interpreter or its success flags.

This operation checks branches, not a guard. Its semantic consumers explicitly
require an actual Value proof that the guard equals the original parameter t,
as well as t in [0,1] and enclosed coordinate values. They prove existence of
an actual conditional value, and enclose each actual value using a witness for
the active cell's local parameter. Strict t<q selects the true branch; equality
selects the false branch. The two local affine cover lists must not be appended
as though their parameters were global. An independent affine regression shows
that doing so gives an incorrect enclosure.

If every component hull in both results excludes zero, a corollary excludes
actual conditional zeros. This requires no continuity. Definedness alone never
supplies continuity or a root from endpoint signs; the existing threshold
continuity certificate still requires its separate boundary/continuity premises.
External partial-coordinate-domain membership remains a caller obligation.

The fresh core-only ThresholdCertificates fixture independently proves the
semantics of `if t<1/2 then 1/(t-1) else 1/t`. Whole-range conditional evaluation
is unknown, while the two branch-local checks succeed. The new certificate
proves definedness and zero exclusion across [0,1], including equality on the
right. Opposite endpoint signs do not imply a root across this jump. An actual
pole in the false branch at equality is both semantically undefined and rejected
by the local check. Successful constant-branch checks with an undefined guard
cannot satisfy the guard premise, and therefore cannot certify the expression.

Closed cells deliberately impose an extra sufficient condition: the true branch
is checked at q even though it is inactive there. A separate example with a true-
branch pole only at q returns unknown although its conditional is everywhere
defined. This is explicit incompleteness, not a claim of absence. Open-cell
arithmetic, arbitrary guard preimages, automatic guard identity inference,
per-component domains, resource budgets and full domain inference are outside
this bounded bridge. There are no additional FP assumptions or continuity claims.

### Inactive-pole failure: two different causes

The post-#42 regression strengthens the earlier conservative-failure example:
its active reciprocal values are unbounded below. Uniform boundedness of every
finite affine cover proves that neither a global cover nor a left-local cover
exists for the complete active range. Removing the inactive endpoint alone
therefore cannot make this example return a successful finite range.

A removable singularity provides the contrasting control. Replacing the true
branch with `(t-1/2)/(t-1/2)` and the false branch with 1 still gives unknown from
the closed-cell checker, while actual semantics have the singleton cover {1}.
A future guarded simplification could address this bounded case, provided it
carries the nonzero premise and never assigns a value to the inactive division
by zero. The current checker and its conservative unknown result are unchanged.

### Proof-directed guarded cancellation

GuardedSimplification proves the exact relation-preserving rewrite
`if g<q then (g-q)/(g-q) else b` to `if g<q then 1 else b`. In the active true
branch, an actual guard value u<q supplies the proof u-q≠0. The guard itself
and the entire false branch are retained. Thus undefined guards stay undefined,
equality still selects b, and partial false branches retain their holes.
The theorem is bidirectional for every coordinate pair and result value; it
preserves actual domains, not merely enclosure of already-defined values.

A small self-division lemma requires an actual nonzero operand value explicitly.
The separate `evalConditionalCover_equivalent_sound` theorem evaluates an
explicitly chosen equivalent expression using the unchanged interpreter, then
transports all three SoundOn obligations to the original expression and the same
partial coordinate environments. Rule selection is explicit: no syntactic
matcher, general simplifier, conditional deletion, or automatic equality solver
is introduced. No value is assigned to unguarded 0/0.

The independent ThresholdCertificates fixture retains its direct proof that the
removable-singularity example has actual value one. It now computes a successful
cover for the rewritten expression and transfers the result to the original
relation, where previous whole/closed-cell analysis was unknown. The resulting
cover contains two exact-one components. It proves endpoint existence and zero
exclusion while retaining an external coordinate-domain hole at 1/4. Controls
retain undefined guards, a false-branch pole at equality and its unknown result,
and reject unguarded self-division at zero. The earlier unbounded reciprocal
example and its no-finite-cover proofs remain unchanged: the cancellation rule
does not apply to that different expression.

This is a bounded improvement for removable singularities with a guard-provided
nonzero proof. It adds no FP assumptions, unbounded ranges, continuity inference,
resource policy or broad evaluator rewrite. It does not claim arbitrary
removable-singularity detection or complete symbolic simplification.
