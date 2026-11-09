> Historical relgraph record: old paths and checks describe their original context.
> For the standalone layout and fresh verification, see [MIGRATION.md](MIGRATION.md).

# Integration and thesis coverage assessment

Original snapshot (preserved below): 2026-11-06, after #24 at `2f98daf614c14a44b5a32b7247ff13feae083605`.
This is a consolidation assessment, not another arithmetic feature. It combines
source inspection of the semantic boundaries, dependency/ancestry checks,
fresh end-to-end Lean regressions, and audit enforcement controls. It is not an
independent human review or a verification of Lean/mathlib/compiler internals.
No blocking soundness defect was identified in the inspected interfaces. The
main shortcomings are coverage, precision, duplication, and review scale.

## Original stack and merge risk

All #11–#24 PRs were checked through GitHub: open, unmerged, and mergeable at
this snapshot. Their remote heads match the local 14-commit linear history from
main `158074aaf8df30242efd5b5c40a562bdcacfafd7`. Each targets its immediate
predecessor, except #11, which targets main. All cumulative changes are confined
to formalization/lean: 50 files, 5,179 added and 49 removed lines before this
consolidation. These are scope counts, not evidence of correctness.

| PR | Original head | Mathematical role |
| --- | --- | --- |
| #11 | `6a00fff` | Continuous-segment root existence, ordinary evaluator continuity |
| #12 | `f0ede15` | Executable segment certificate and three-way classification |
| #13 | `b750c95` | Finite search; optional eight-segment policy |
| #14 | `56cf5b9` | Ordinary-box subdivision and coverage |
| #15 | `892e350` | One-parameter linear bounds and relational domain contracts |
| #16 | `97c6dda` | Linear product enclosure and joins |
| #17 | `602ddb8` | Enforced transitive axiom policy |
| #18 | `22817a3` | Polynomial linear evaluator |
| #19 | `e8b4d03` | Whole-hull guarded reciprocal/division |
| #20 | `d6355f0` | Domain-local coordinate semantics |
| #21 | `df548a0` | Guarded linear evaluator and compatibility |
| #22 | `91db4d7` | External piecewise value/domain selection |
| #23 | `3adad1a` | Partial guards and active-branch conditional trees |
| #24 | `2f98daf` | Exact arithmetic distribution through conditional trees |

Mergeability is only Git's conflict status. It says nothing about mathematical
review, tests, or approval. Do not merge from this report. When merging is
separately authorized, work from the bottom and verify ancestry/base/diff after
each step. Squashing a predecessor can make downstream PRs show already reviewed
commits; retargeting alone is not a guarantee of a clean incremental diff. Do not
force-push/rebase the stack as an incidental cleanup. Base edits may invalidate
later review conclusions and require rebuilding the integrated head. There is
no hosted CI or branch-protection evidence supplied by this work.

## What is actually connected

There are two consumers of the common partial Expr/Value semantics:

- Ordinary rational intervals plus a conditional rounding adapter feed
  ExpressionContinuity, presence, search, and subdivision. Presence derives
  continuity and definedness from successful whole-box arithmetic evaluation.
- Exact rational, one-parameter linear intervals feed polynomial/guarded
  interpretation, relational domain contracts, partial conditionals, and
  arithmetic distribution. This path does not feed the graph presence checker.

The two paths share semantics, not a proved general equality or precision order
between their results. The exact polynomial-to-guarded compatibility theorem and
leaf compatibility for conditionals/arithmetic are narrower proved connections.
A successful generalized/conditional enclosure is not a continuity certificate.
The discontinuous-jump controls are essential and must survive consolidation.

PartialEnclosure.Sound has three distinct obligations: enclosure, possible
membership for actual values, and existence from definite membership. It is a
semantic contract over arbitrary predicates/real functions. It is not an
executable analyzer. The interpreters accept or reject whole numerical bounds;
caller domain predicates do not tighten those guards. A failure yields unknown,
not an empty relation. Guarded/conditional definedness is local to certified
parameters/enclosed coordinates; polynomial definedness has a stronger global
statement because successful polynomial evaluation excludes all division syntax.

Coordinate relations remain strict and separate: both bindings must exist, even
for constants, and the context is a Cartesian product of unary relations. This
is explicit and sound for that semantics. It does not implement minimal-variable
or arbitrary joint-domain environments. Repeated variables in expression values
share chosen coordinates, but intervals may lose their correlation. Operand
relations in generic sum/product/quotient operators are intentionally independent
at a parameter; equal interval descriptions do not justify cancellation of two
independent values.

## Thesis coverage, without equating milestones to completed chapters

The [thesis contents](https://www.dgp.toronto.edu/~mooncake/thesis/node1.html)
shows a substantially broader project than this stack. The following is our
coverage assessment, not a statement that the thesis prescribes these APIs.

| Thesis area | Present | Important missing foundation or capability |
| --- | --- | --- |
| §2.7–2.9 basic and generalized intervals | Rational bounds, inclusion proofs, one affine parameter | A uniform representation/refinement interface and proved conversion laws; quadratic/multiple-parameter models |
| §2.9.3 linear intervals | Shared parameter, exact affine cancellation, sound product demotion | General parameter restriction/reparameterization and precision/refinement laws |
| §2.9.6–2.9.7 broader representations | Functional bounds in a semantic contract | Executable multidimensional/functional arithmetic; current x/y inputs do not create two independent affine parameters |
| §2.11 domains; §3.3.16 partial functions | Explicit partial values and definite/possible predicates | Executable domain descriptions, domain-sensitive primitive models, and numerical restriction of the working parameter range |
| §2.12 properties; §3.3.18 discontinuities | Separation of values, domains, and continuity; negative controls | Compositional continuity/property certificates for generalized arithmetic and conditional boundaries |
| §2.13 interval sets | Multivalued relations can be described semantically | A finite interval-set representation and certified operations/coverage |
| Chapter 3 operator methods | Four basic arithmetic operations with one chosen product bound and reciprocal fallback | Monotonicity/convexity-based model framework, transcendental/periodic functions, polynomial interval arithmetic |
| Chapter 4 graphs | Ordinary empty/present/unknown certificates, finite search/subdivision | Generalized-arithmetic integration, full relation/Boolean syntax, raster semantics and rendering correctness |
| §4.4–4.5 optimization | Exact conditional arithmetic transformation and certified choices | Sharing/caching, path-condition propagation, cost models and verified optimization |
| Floating point | Outward-rounding contracts and conditional ordinary backend theorem | Concrete IEEE formats, overflow/NaN/infinity semantics, rounded linear coefficients and machine execution proofs; not expanded without discussion |

[Linear intervals](https://www.dgp.toronto.edu/~mooncake/thesis/node39.html)
retain dependence but do not promise a universally best linear demotion. Our
product policy is one sound choice, not a formalization of all thesis models.
[Multiple parameters](https://www.dgp.toronto.edu/~mooncake/thesis/node42.html)
and [functional bounds](https://www.dgp.toronto.edu/~mooncake/thesis/node43.html)
are real extensions still missing from the executable library.
[Domains](https://www.dgp.toronto.edu/~mooncake/thesis/node46.html) and
[partial-function models](https://www.dgp.toronto.edu/~mooncake/thesis/node122.html)
track information beyond whether a whole interval operation succeeds. Our
predicate contracts specify obligations but do not reproduce that numerical
machinery. [Property tracking](https://www.dgp.toronto.edu/~mooncake/thesis/node52.html)
and [continuity descriptions](https://www.dgp.toronto.edu/~mooncake/thesis/node124.html)
make the missing continuity layer explicit.
[Interval sets](https://www.dgp.toronto.edu/~mooncake/thesis/node56.html) are not
implemented merely because our semantic relations permit multiple values.
[Continuity-based testing](https://www.dgp.toronto.edu/~mooncake/thesis/node156.html)
is a useful application, but its ordinary implementation is not coverage of the
entire graphing chapter. Formula images were not transcribed in this assessment;
no exact numerical encoding is asserted from the HTML prose alone.

## Duplication and maintainability

1. evalLinear and evalGuarded duplicate structural recursion and enclosure proofs.
   Keep evalLinear as the explicit polynomial fragment for now: its global
   definedness theorem must not be generalized accidentally. Prefer evalGuarded
   for new arithmetic clients. Later refactoring should preserve exact old-result
   compatibility and separate local/global theorems before removing duplication.
2. Several private Option-success decomposition helpers and relational contract
   proofs repeat. A small common helper module is plausible, but a highly generic
   evaluator framework is not justified solely to reduce line count.
3. DomainBounds.inter and LinearInterval.onDomain live in LinearMultiplication;
   PiecewiseSelection imports GuardedEvaluator for its integration theorem.
   These are organizational dependencies, not mathematical necessities. A future
   module cleanup can separate domain primitives and pure selection from clients.
4. SumValues, ProductValues, QuotientValues, and ConditionalArithmeticValue are
   variants of existential relational lifting. A common relation combinator may
   help once the next domain API is settled; merging them now could obscure the
   nonzero and active-branch conditions.
5. The conditional tree transformation is a useful exact semantic specification,
   not a scalable compilation strategy. It duplicates trees and can retain
   unreachable correlated paths. A direct evaluator/shared AST must be checked
   against the equivalence theorem, not replace it by intuition.
6. Historical milestone notes describe earlier limitations. Read this assessment
   and the current module map first; preserve historical validation as evidence.
   The growing manual named audit list is a landmark list, not the sole coverage
   mechanism. Namespace enforcement plus the new module-reachability control are
   the safety net, within their documented trust scope.

## Consolidation checks and bounded changes

`./check.sh` runs the default Lake build, a fresh standalone Audit invocation,
and Python standard-library tests. Python 3.11+ is required for tomllib; this is
local formalization tooling, not an application dependency or hosted CI.

The existing eight independent-process policy tests exercise accepted standard
axioms and rejected placeholders/custom axioms, including transitive and unnamed
namespace dependencies. New coverage checks use Lean's own `--deps` output to
verify all root modules are registered, default-built, and reachable from Audit.
They reject a missing default Audit target, an unregistered source, and an
omitted module in synthetic negative controls. The current flat source-layout
policy is explicit; adding nested source modules requires updating it.

`tests/Integration.lean` imports implementation modules, not milestone example
fixtures. It checks new box/quotient/conditional instances and connects executable
results to no-root, defined-root, nonzero, and partial-domain conclusions. Its own
namespace axiom audit is mandatory in the test process. These are independently
constructed regressions, not an independent proof checker.

All 36 library modules were already covered at #24; no omitted existing proof
was discovered. The coverage control prevents future accidental omission. It
does not extend the axiom policy to arbitrary other namespaces, unused
implementation definitions, or compiler artifacts, nor stop intentional edits
to the validation tooling. No mathematical API, FP assumption, pin, native build,
or hosted CI changes in this consolidation. Exact run evidence is appended to
VALIDATION.md.

## Highest-value next step

First stabilize review of the existing stack. Then prioritize a small parameter
restriction/reparameterization foundation over a larger conditional AST:

- For rational 0 ≤ a ≤ b ≤ 1, compute affine endpoint bounds for the map
  s ↦ a + (b-a)s and prove exact containment correspondence for s in [0,1].
- Prove coverage for finite closed subintervals, including shared boundaries and
  degenerate cells, and transfer actual partial-value/domain relations through
  that map. Do not equate domain predicates with a numerical restriction.
- Exercise existing guarded arithmetic on those restricted models. Accept a
  reciprocal on a certified cell away from zero; keep a zero-touching cell
  unknown. Recombine enclosure claims only under the proved cover.

This would connect the general arithmetic to usable domain-sensitive evaluation
without inventing an FP model or adding graph-specific search. It also supplies
a concrete prerequisite for later finite pieces/interval sets. Closed-cell
coverage alone will not resolve strict conditional boundaries; retain unknown
there until a separate boundary/path certificate is supplied. Do not claim
continuity, maximal domains, completeness, or all repeated-guard correlations
from restriction. A general executable domain representation and automatic
continuity tracking should follow as distinct designs, not be silently bundled
into this next bounded theorem.

Follow-on: [parameter restriction](PARAMETER_RESTRICTION.md) implements the
bounded reparameterization and supplied-coverage foundation proposed above.
The coverage matrix and counts here retain their #24 snapshot meaning.

The later [semantic continuity bridge](SEMANTIC_CONTINUITY.md) proves relative
continuity for defined arithmetic with continuous coordinates, with guarded and
restricted-cell corollaries. General property tracking and cross-cell/conditional
continuity remain outside that bounded extension.

The subsequent [closed-cell continuity module](CELL_CONTINUITY.md) composes a
common function over finite closed covers. Local representatives require proved
agreement, and semantic definedness remains a separate obligation. Automatic
conditional/property analysis is still outside this extension.

The later [conditional continuity rule](CONDITIONAL_CONTINUITY.md) adds supplied
certificates for parameter-threshold guards with matching continuous branch
representatives. Arbitrary guard crossings and automatic property analysis are
not inferred from that sufficient rule.

## Follow-on: finite linear covers

The finite-cover milestone addresses the interval-set gap in a bounded form:
finite unions reuse existing linear bounds, branch decisions, and guarded
reciprocals. Evaluator results feed the union contract directly. Separated
constant and varying branch examples demonstrate useful zero exclusion and
reciprocation unavailable after convex joining. The API remains enclosure-only;
domain existence and continuity certificates are retained independently.
Full finite-cover expression interpretation, normalization, general set
arithmetic, and executable domain discovery remain open. This is a foundational
range representation, not another extension of expression syntax.

## Follow-on: conditional cover/domain integration

The cover-valued interpreter now connects the finite-range representation to
existing conditional syntax and actual relational semantics. Its success flags
are proved equal to the scalar interpreter's; only range joining changes.
Finite-cover domain soundness and guarded reciprocal composition carry definite
and possible domains separately from range membership. The punctured-environment
jump regression exercises evaluation, exclusion, reciprocal enclosure, absence,
and existence together. Minimal-domain inference, general cover arithmetic,
normalization/resource policies, and continuity tracking remain separate gaps.

## Follow-on: domain-certified cover presence

Finite-cover domain contracts and existing conditional continuity certificates
now compose into an actual relational-root theorem. The key obligation is
whole-path definite definedness, separate from continuity of a representative.
A two-slope conditional supplies a positive end-to-end certificate; deleting its
unique zero from the domain preserves endpoint values and bounds but destroys
root existence. This closes a semantic integration gap without adding syntax
or weakening unknown outcomes. Automatic continuity/domain certificate discovery,
general multivalued root rules, and executable resource policies remain open.

## Follow-on: inclusion, scalar bridging, and output-size control

Finite-cover inclusion now transports enclosure and the same domain contract;
a singleton equivalence reconnects the representation to existing scalar partial
enclosures. Optional full coalescing supplies a verified output-length bound,
addressing one part of the earlier representation-size gap. The policy leaves
interpreters unchanged and does not bound intermediate evaluation work or memory.
Tests demonstrate both genuine precision loss and preservation of domain/root
certificates. Executable inclusion tests, optimal normalization, and evaluator
resource accounting remain open; no stronger performance claim is inferred.

## Follow-on: finite-cover parameter restriction

The original exact cell change of parameter now applies to finite covers and
preserves their inclusion and domain contracts without a second subdivision
interface. A fresh conditional-evaluation bridge reuses the existing interpreter.
An independent two-valued relation shows that restriction/coalescing order can
change reciprocal success despite identical sound domain descriptions. The
single-representative premise of the presence theorem is explicitly refuted for
that relation. Degenerate cells preserve missing values; fresh local guard
analysis can remove branches that plain reparameterization retains. Automatic
cell selection, optimal operation ordering and multivalued continuity/presence
rules remain open; none is inferred from these sufficient certificates.

## Consolidation after #35: 2026-11-06 23:45 UTC

This round adds no core API or arithmetic feature. The highest-value gap was
fresh-client integration coverage: the original independent fixture predated
finite covers, their domain contracts, coalescing and cell restriction. Milestone
examples exercised those operations, but the separate fixture did not.

`tests/CoverPipeline.lean` now imports only public core modules and AuditPolicy.
It uses a new variable-valued choice: below 1/4, -(t+2); otherwise t+2. The
coordinate environment omits t=1/2. On [1/4,3/4], fresh interpretation, limit one,
and guarded reciprocal compose into exact bounds [4/11,4/9] with the pulled-back
domain contract. Both local endpoints have actual values and zero is excluded,
while the interior domain hole persists. The expression itself is separately
proved defined at that excluded coordinate, preventing conflation of the two
semantics. Global limit one makes reciprocal evaluation unknown; limit two
succeeds; zero capacity remains unknown. These outcomes are concrete kernel
checks alongside semantic contracts, not just aliases of milestone examples.

The test runner now registers every persistent Lean fixture, runs each freshly,
and requires its namespace audit. Lean's dependency graph verifies that both
fixtures avoid transitive imports of `*Examples` modules. Independence here
means a separate client of the core interfaces; it is not a second evaluator,
independent theorem prover, or mathematical review by another person.

### Updated review preparation

All 24 GIA PRs #11–#35, excluding unrelated #31, were read through GitHub. All
were open and unmerged, with exact predecessor base/head matches. The local
first-parent history from `158074a` to `a72069e` agrees with all 24 remote heads.
The full current table is at the top of REVIEW_STACK.md. Historical status and
validation entries are preserved. No merges, base edits, rebases or force pushes
were performed. The size of the stack is a review risk even though its ancestry
is clean; review in predecessor order and recheck actual diffs after any future
separately authorized merge.

### Interface assessment and remaining mathematical gaps

- The scalar and cover conditional interpreters have different range return
  types, with exact success-flag correspondence proved. Polynomial/guarded
  evaluators similarly retain explicit compatibility results. A generic range
  algebra might reduce implementation duplication, but refactoring this whole
  stack before review would create avoidable proof and diff churn. No such
  refactor was needed to make the public pipeline compose.
- PartialEnclosure and finite-cover SoundOn carry the same three semantic
  obligations with different range representations. The singleton equivalence
  is a useful existing bridge; replacing them with another shared abstraction is
  not currently necessary. Domain predicates remain semantic, not inferred
  executable maximal-domain descriptions.
- Single-parameter linear bounds do not implement the thesis's multidimensional
  or richer functional/symbolic interval systems. Separate coordinate relations
  and mandatory coordinate environments remain conservative for joint domains.
- Finite unions now support conditional interpretation, reciprocal enclosure,
  restriction and sound coalescing. They do not implement general interval-set
  arithmetic, unbounded ranges, optimal normalization, or multivalued continuity
  and root rules. The #35 counterexample prevents treating every relation as a
  single-valued representative.
- Continuity, definite whole-path membership and boundary agreement are supplied
  proof obligations. The semantic presence rule does not make the generalized
  arithmetic path an automatic graph classifier. The existing executable graph
  search/subdivision remains the ordinary-interval path.
- Output-size limiting does not bound intermediate evaluation resources or the
  duplication caused by arithmetic-tree distribution. Adding such a bound needs
  a specified evaluator policy and proof, not a stronger label on postprocessing.
- Directed-rounding assumptions remain abstract. No IEEE 754 bit-level behavior,
  transcendental library correctness, or application implementation is verified.

The thesis links and qualified coverage map in the original assessment and
milestone notes remain the references for these gaps. After review consolidation,
a higher-value next integration would be a bounded producer/consumer of explicit
cell-domain and continuity certificates, with clear unknown outcomes, before
adding more syntax. That recommendation is a direction for assessment, not a
claim that arbitrary domain or continuity inference is decidable or implemented.

## Follow-on: fuelled supplied-cell certificates

A bounded certificate producer now reuses evalGuarded over supplied ParameterCells.
Its cost model counts top-level evaluator attempts; the proved counter never
exceeds fuel and a certified list has checked every member. Exhaustion and failed
enclosures return unknown. This does not bound arithmetic cost or preempt a long
individual call, and no evaluator was duplicated or broadly refactored.

With a separate ParameterCover proof, local successes establish pointwise Expr
values. Existing arithmetic semantic continuity then derives a whole-path
certificate for continuous enclosed coordinate functions. A fresh core-only
fixture obtains a root where whole-interval evaluation fails, and separately
shows that skipped gaps can hide poles and that unknown under exhaustion does
not imply absence. Arbitrary domain predicates, conditional continuity, automatic
cell generation/coverage discovery and whole-program resource bounds remain
outside this step.

## Follow-on: automatic validation of supplied cell coverage

A conservative rational endpoint scan now proves ParameterCover for accepted
lists. The combined certificate first validates geometry, then reuses checkCells;
no expression evaluator or subdivision algorithm is copied. Arithmetic
continuity/definedness can therefore be derived without a caller-written
coverage proof. The independent actual-root pipeline now exercises this route.

Order sensitivity is explicit: a true reversed cover can return unknown.
Overlaps, nested cells and shared endpoints are handled, while gaps and empty
lists fail before evaluation. Redundant cells still consume arithmetic fuel;
geometry scanning is not charged to the evaluator-call counter. Coordinate
continuity/enclosure and external environment membership remain obligations.
Automatic cell generation, complete coverage recognition through sorting,
minimal-cover extraction and whole-program resource accounting remain separate
choices rather than being silently added to this bounded step.

### Adaptive cell integration (after #38)

A depth-bounded producer now reuses midpoint geometry and the existing single-
cell checker; final validation reuses the coverage front end. This closes the
manual cell-list gap for a sufficient arithmetic domain/continuity path without
adding syntax. Unresolved leaves remain in the cover. The independent root
fixture now uses generated cells, while a pole cannot be certified for any
budgets. Planning and revalidation are separately bounded and jointly counted.
Repeated checks are an explicit maintainability tradeoff; caching and completeness
of the ordered scan on generated lists are not proved. General conditional
continuity, external partial-coordinate membership and richer generalized
interval domains remain separate gaps; no broad rewrite is warranted here.

### Finite-cover multiplication (after #39)

The next foundational gap selected was arithmetic on finite unions, rather than
another adaptive-search interface. Re-reading thesis §§2.13–2.13.1 supports
union membership and independent component choices; the existing ProductValues
and DomainBounds.inter already specify the required relation and domain contract.
A small Cartesian multiplication layer now reuses linear_mul_encloses and proves
both enclosure and SoundOn without another evaluator or abstraction hierarchy.

Fresh integration composes the restricted conditional reciprocal pipeline with
multiplication and coalescing, retaining actual values and a domain hole. A
multivalued ±1 control rejects zipped pairs and distinguishes independent choices
from correlated squaring. Shared-parameter dependence is retained; witness/branch
correlation and per-component domains are not inferred. Other finite-cover binary
operations, richer domains, normalization and intermediate resource control remain
open. This step is general arithmetic and does not expand graph-specific APIs.

### Shared witness versus Cartesian growth (after #40)

A generic correlated binary interpreter would need a specification of shared
choices or a joint relation, while a runtime resource cap would need an execution
cost policy. Neither warrants a broad rewrite now. The bounded chosen case is
unary square: one witness is explicitly reused, and each input component yields
one self-product. Existing linear multiplication and SoundOn suffice. A proved
single-valuedness bridge states exactly when it agrees with the independent
ProductValues relation; equal lists alone do not justify that substitution.

The core-only client ties this to both partial-domain semantics and resource
policy: conditional/restricted squaring and reciprocal preserve an actual hole;
±1 alternatives square exactly to one; early coalescing loses a reciprocal
certificate while late coalescing succeeds. This makes the representation-size
tradeoff visible without adding another policy or evaluator. General witness
correlation, per-component domains and whole-evaluation resource accounting
remain open. No decision requiring FP assumption changes was needed.

### Threshold-local domain bridge (after #41)

The independent post-#41 diagnostic exposed an integration gap: inactive poles
can defeat whole-range conditional evaluation even when every active branch is
defined. A bounded bridge now evaluates the two branches on their closed rational
threshold cells and uses map-onto plus the existing local soundness/definedness
proofs. It introduces no alternate evaluator, general domain representation or
continuity inference. A pair of local covers preserves parameter provenance.

Specification checks distinguish branch success from actual guard identity,
strict selection from false-branch equality, and local versus global affine
parameters. The fresh fixture independently checks semantic definedness/no-zero
for a jump, then derives those conclusions through the new bridge. An active
boundary pole is rejected; an inactive boundary pole illustrates conservative
closed-cell failure. All these are arithmetic/domain claims, not continuity or
root-presence certificates. Next substantial gaps remain general guard preimages
and domain-conditioned enclosures; no generic domain API is warranted without a
similarly precise executable contract.

### Representation limit before relaxing closed-cell checks (after #42)

The next increment is foundational verification, not another checker API.
Every finite rational affine cover is uniformly bounded on its unit parameters.
The inactive-boundary reciprocal example has actual values below every real
bound strictly inside its active branch. It consequently admits neither a
finite global cover nor a finite cover in the left cell's local parameter.
Open endpoints or more finite components alone cannot repair that example.

The bounded removable-singularity control identifies a different issue:
`(t-1/2)/(t-1/2)` on the active branch has an exact-one cover when the branch's
nonzero premise is supplied, despite current checker failure. This is a precise
candidate for a later proof-carrying arithmetic simplification, not permission
to replace x/x universally. Unbounded range support is a separate substantive
representation choice; it should not be smuggled into a boundary-check change.
The current APIs and unknown outcomes remain intact, with no FP complications.

## Executable domain-query prerequisite (2026-11-07)

This increment starts directly at merged main
`8ce2199f6d2d72c0c47269d02b8e1f1aa8cde7f0`, keeping #44 and #45 outside its source
and build dependency closure. Because #45's numerical quotient certificates
remain under review, this change does not duplicate them or pull their source
into main. Instead it adds one generic query on existing `DomainBounds` and five
proofs. Its domain-only semantic wrappers are designed to consume #45's two
quotient certificates without requiring a bounded quotient range. See validation
for a separate compatibility check of that composition against #45's exact head.

The next missing step remains executable numerical membership descriptions and
composition for general expressions; this query layer only executes already
decidable descriptions. The committed rational fixture independently validates
partial expression semantics, domain intersection, boundary handling and unknown
results. No new interval representation or evaluator is needed for this step.

## Restricted automatic quotient-domain integration (2026-11-07)

This branch builds on #46 and includes the unchanged 55-line `NonzeroDomains`
module from #45 head `9fb779e8843c317b30bdcca5097949c98083d43b` as an explicit
prerequisite; neither PR is modified or merged. The new work reuses both
foundations in a single kernel-checked pipeline: guarded child evaluation,
rational numerical domain refinement, then the existing three-way query.
Review the five public theorems in `QuotientDomains` and the fresh fixture's
independent semantic controls. The imported #45 module is not a second API.

A bounded outer-quotient analyzer avoids a new symbolic constraint language or
an alternative expression evaluator. The significant remaining restriction is
failure on nested children whose whole-hull analysis is unknown: pointwise domain
knowledge is not fed back into their range evaluator. Extending that safely needs
an explicit compositional range/domain design; this increment makes no such claim.

## Exact-point completeness as a precision path (2026-11-07)

The nested-child limitation from #47 can be improved for exact rational inputs
without changing the uncertain-interval evaluator. This increment, based on
#47 head `00d1a4914e816da96ccee9449b05610602194556`, proves singleton completeness
for the original `eval exactBackend` and reuses its existing recursion. No new
recursive interpreter or symbolic constraint language is introduced.

The scope is exact coordinate values, not uncertain coordinate intervals. The
new point domain contains both positive and negative certificates justified by
completeness, whereas the older range analysis retains unknown on failure.
Independent counterexamples enforce this distinction for wide intervals and a
sound declining backend. External domains remain explicit. General recursive
range/domain analysis over uncertain inputs is still open and would need a
separate representation/design choice; this result does not silently choose one.

## Feasibility of recursive uncertain-input domains (2026-11-07)

Assessment base: #48 head `404271d5b6e19c2df89825e4446afb5671c28548`.
No new analyzer or production mathematical interface is added. The fresh
`tests/UncertainDomains.lean` makes two design obstacles explicit using existing
partial semantics, domain contracts, and finite-cover theorems.

### Shared-input domains must survive composition

Let the allowed uncertain input be `{−1, 1}`, and let
`a = 1/(x−1)` and `b = 1/(x+1)`. The fixture independently proves that the
projected value relation for `a` is exactly `{−1/2}` and for `b` exactly `{1/2}`.
Both have sound partial enclosures with definite domain membership. The existing
`partial_add_sound` correctly supplies zero for their **independent-witness**
`SumValues` relation. But the AST `a+b` has no defined value at any common allowed
input. A theorem explicitly refutes reinterpreting that enclosure as a sound
shared-input expression enclosure.

The logical issue is projection order:
`(∃ x, A x ∧ defined a x) ∧ (∃ x, A x ∧ defined b x)` does not imply
`∃ x, A x ∧ defined a x ∧ defined b x`. Thus recursive intersection of the
current projected existential certificates is insufficient. No current theorem
asserts this implication: `ProductValues`, `SumValues` and `QuotientValues` state
their independent witnesses; the expression semantics retains one coordinate
pair. #47 fixes the coordinate functions, and #48 uses exact points, avoiding
this mismatch.

A positive control proves the safe alternative: an actual common input plus
**uniform** child-definedness over the allowed inputs composes. The current
successful guarded evaluator already provides this style of guarantee. In the
counterexample neither child is uniformly defined, and current guarded analysis
remains unknown. The hull midpoint zero makes the arithmetic sum defined, but
it is explicitly excluded by the original input relation. Sampling that midpoint
cannot replace external-domain evidence.

### A finite union does not remove the pole representation limit

A second relation allows any nonzero `x` in `[-1,1]` at one fixed parameter and
contains the actual values of `1/x`. The fixture constructs values below every
real lower bound, then applies the existing `no_finite_cover_of_unbounded_below`
theorem. Therefore no finite union of the current bounded affine intervals
covers this uncertain-input reciprocal range. This is not absence or unknown
domain membership: it is a restriction of the available range representation.
Adding more finite components alone cannot resolve it.

### Thesis alignment and next design boundary

Tupper's [§2.9.6](https://www.dgp.toronto.edu/~mooncake/thesis/node42.html) retains
multiple parameters, and [§2.11.4](https://www.dgp.toronto.edu/~mooncake/thesis/node50.html)
describes domains by conjunctions of constraints at a parameter value.
[§2.13](https://www.dgp.toronto.edu/~mooncake/thesis/node56.html) introduces sets of
interval descriptions, including multifunctions. My design inference is that
our shared coordinate environment must remain available while those constraints
are combined; separately existentially projecting child domains loses essential
information. These tests do not claim to formalize the thesis's full constraint
language or multidimensional interval system.

| Direction | Assessment |
| --- | --- |
| Retain uniform guarded certificates and unknown on failed analysis | Sound and already supported; no new feature is justified merely by wrapping it again. |
| Intersect independently projected child existence domains | Unsound for shared-input expressions; explicitly refuted by the fixture. |
| Retain domain constraints indexed by the full common environment, project only after composition | Recommended semantic direction; executable constraint representation and projection policy need a separate design. |
| Carry domain evidence with an unavailable range | Conservative candidate for poles; outer operations must remain unknown unless separate properties justify them. |
| Replace finite bounded ranges with unbounded/extended ranges | Broader representation change; not selected or implemented. |

Before another general recursive inference implementation, specify a small
shared-environment constraint contract and how to represent missing range
information. `DomainBounds α` can already express a richer index semantically,
but that alone is not an executable analyzer. This assessment preserves all
existing APIs and assumptions, external holes, and unknown outcomes. It does not
claim that sound recursive uncertain-input analysis is impossible—only that the
naive projected-domain composition and finite-range-only approach are inadequate.

## Representation comparison and isolated prototype (2026-11-07)

Comparison base: #49 head `a68996dfac7b4036d674e9d4327039221199e76f`.
These choices have two separate axes: how to retain the common environment and
its domain constraints, and how to represent numerical ranges. Richer ranges do
not by themselves repair independently projected input witnesses.

| Representation | Main advantage | Cost / unresolved issue | Fit with current code |
| --- | --- | --- | --- |
| Shared-environment domain predicates plus optional current bounds | Retains domain evidence even when no finite enclosure is available; preserves common inputs through composition | Arbitrary predicates are semantic, not an executable constraint language; absent ranges often force later partial operations to remain unknown | Reuses `DomainBounds α`, `FunctionalBounds`, `PartialEnclosure`, existing addition and query contracts; smallest reversible extension |
| Finite partitions of the shared input environment, with a domain/range summary per cell | Makes local nonzero guards and finite enclosures available on many cells; supports resource-bounded precision improvements | Must preserve coverage, overlaps, external holes and environment identity; combining independently partitioned operands may require a common refinement; cells meeting poles can remain unknown | Reuses subdivision/coverage ideas, but current `ParameterCell` is one-dimensional and cannot silently become a full `(parameter,x,y)` partition |
| Functional or symbolic bounds indexed by the full environment | Can retain dependencies and describe some pole behavior on a restricted domain without bounded affine hulls | Executable interpretation, simplification, decidable guards and complexity become the hard part; an unevaluated expression is not automatically useful numerical progress | Existing functional bounds provide semantics, but executable affine models would need additional certified models |
| Unbounded mathematical endpoints / unions, retaining the same environment constraints | Can express reciprocal rays that current finite bounded components cannot enclose | Requires new endpoint/order/arithmetic and partial-domain rules; still does not solve witness correlation or general domain decisions | Largest range-model change; current finite-cover boundedness theorems intentionally do not apply |

### Relationship to the thesis

[Tupper §2.11.4](https://www.dgp.toronto.edu/~mooncake/thesis/node50.html) permits
conjunctions of domain constraints at a parameter. This supports retaining the
same parameter/environment until constraints are combined; it does not license
conjoining separately projected existential witnesses. The environment-indexed
proposal is our implementation interpretation, not a claim that the current
predicates implement the thesis's numerical encoding or demotion rules.

[§2.13.1](https://www.dgp.toronto.edu/~mooncake/thesis/node57.html) discusses the
tradeoff between expressive interval-set descriptions and manageable description
size. Cell partitions and finite unions are useful precision mechanisms, but our
#49 proof shows bounded finite components cannot cover a genuine unbounded
reciprocal range. A parameter partition is also not the same thing as a union of
output bounds; it must carry input coverage and provenance.

[§2.9.7](https://www.dgp.toronto.edu/~mooncake/thesis/node43.html) explicitly links
the choice of bound functions to model/demotion complexity and precision.
[§2.9.8](https://www.dgp.toronto.edu/~mooncake/thesis/node44.html) cautions that
symbolically retaining a computation can defer the difficult interpretation
rather than solve it. This is a reason to start with a small certified constraint
fragment rather than a general symbolic engine. The thesis's extended-real
model is a further separate subject; no IEEE 754 or extended-value arithmetic
assumptions are introduced by this comparison or prototype.

### What the proof-of-concept establishes

`tests/OptionalRangePrototype.lean` is test-local and is not imported by any
production module. Its experimental `Summary Env` retains `DomainBounds Env`
and optionally holds `FunctionalBounds Env`. `none` means **no asserted range**;
it is neither an undefined-value flag nor a claim that every real value occurs.
The environment must include the shared inputs whose correlation matters.

Kernel-checked results establish:

- A faithful embedding: the prototype's soundness contract for a known range is
  equivalent to the existing `PartialEnclosure.Sound` contract.
- Forgetting range information preserves both domain directions.
- Addition uses the existing partial-enclosure addition when both ranges are
  present; otherwise it retains a common-environment domain conjunction with no
  range assertion. Both branches are proved sound.
- An exact equivalence connects same-environment `SumValues` to the existing
  expression `Value` semantics. This equivalence fails for separately projected
  environments, as the previous fixture demonstrates.
- A reciprocal with no asserted range is defined at one and undefined at zero;
  its relation is proved equivalent to the existing partial expression semantics.
  Addition can remain definitely defined even with no range available.
- Disjoint child environment domains cannot manufacture a common input. A
  possible-but-not-definite domain with no range supports both absent and present
  models, so it remains genuinely inconclusive.

This is a semantic composition experiment, not automatic domain generation,
projection, a complete recursive analyzer, or a committed replacement API. It
introduces no production module, dependency, FP assumption, or merge.

### Recommendation and decision boundary

Use the first option as the semantic basis for further experiments; treat
partitions as a later refinement mechanism, and defer richer/unbounded range
models. This has a clear reversible benefit: it preserves existing range proofs
and lets domain facts survive a range failure, without claiming new numerical
precision. The prototype is not yet a reason to migrate the production types.

No user decision is needed to retain these tests. Before a broad implementation,
John's priority choice would matter: **symbolic/domain precision first** versus
**numerical range coverage near poles first**. I recommend the former. A bounded
next experiment would use a finite conjunction of rational affine guards over
one shared environment and prove a conservative query, retaining unknown when
membership or projection is unresolved. The prototype has not selected that
constraint syntax, a general solver, multidimensional cell format, or an
unbounded arithmetic model.

## Bounded domain-precision increment: affine guards (2026-11-07)

Based on #50 head `ee23e8e49965bd474237806f55a9327467ed9de0`. The chosen next
increment is a finite conjunction of rational affine nonzero guards at a shared
`(x,y)` environment, paired with a certified expression family (sums of their
reciprocals). It does not migrate existing interval types or adopt the optional
range prototype as a production API. Existing `DomainBounds`, expression
semantics, and query contracts are reused.

The key new result is exact definedness over all real environments, with exact
executable membership at rational environments. Shared-input composition is
explicit and the earlier disjoint-witness counterexample is rechecked. The
external domain can still be uncertain or exclude otherwise valid points.
There is no existential projection algorithm: adding one would require a separate
solver/representation decision. This avoids confusing point membership with
region feasibility and avoids a broad symbolic rewrite. Numerical range coverage
near poles is still deferred. No major user tradeoff was required for this
restricted family; broader constraint syntax or projection remains for review.

## Segment-domain integration (2026-11-07)

The next bounded consumer of affine guards is the existing presence checker.
A whole-box range failure need not prevent certification on a safe segment.
Affine interpolation plus strict endpoint signs establishes the closed-segment
domain, and existing semantic continuity and intermediate-value infrastructure
finish the proof. This avoids a new range representation, search policy or AST.

The implementation is opt-in and restricted to the generated reciprocal sums.
It does not solve arbitrary constraint feasibility, consume external holes,
or certify a path from endpoint membership alone. Tests distinguish a pole
elsewhere in the box from a pole on the path. The latter remains unknown.
A future external-domain consumer would need a whole-path domain certificate,
not merely definite membership of its two endpoints. That design is deferred.

## External-domain integration update (2026-11-07)

The earlier segment integration deferred external-domain consumers. The current
proof interface now retains the actual path parameter and accepts a caller proof
of whole-path inclusion. This discharges the semantic transport step while
leaving automatic construction of external-domain path certificates deferred.
The completeness contract separates arithmetic guards from external membership;
absence restricts without a path premise. An endpoint-only counterexample checks
that the stronger presence premise cannot be replaced with endpoint membership.

## Bounded constructive external regions (2026-11-07)

Automatic path certificates now cover finite conjunctions of closed rational
affine half-spaces, reusing RationalAffineForm, BranchSound and the existing
presence bridge. Endpoint inclusion is sufficient and necessary for this convex
class. A single uniformly violated constraint certifies path exclusion; remaining
cases stay unknown, including some inconsistent conjunctions. This fills a useful
part of the previously deferred automatic path obligation without a general
constraint solver, syntax recognizer or change to value representations.

## Finite search integration under affine restrictions (2026-11-07)

The existing eight center-to-boundary policy now feeds the region and arithmetic
certificates through a finite first-match search, with both sign orientations.
No geometry or evaluator is duplicated. The classifier's empty branch remains
whole-box arithmetic zero exclusion; failed path candidates never imply absence.
The policy is deliberately incomplete when its common center is inadmissible or
undefined. Independent controls show both failures and recovery with a supplied
valid segment. Candidate-policy refinement remains optional future work, not a
reason to weaken domain or presence premises.

## Bounded constrained subdivision (2026-11-07)

The earlier missed-root example now motivates a concrete coverage improvement:
reusing alternating midpoint subdivision moves the candidate center into an
admissible child after two splits. The ordinary recursion is extracted into a
checker-parametric engine with exact root-coverage premises; its previous API and
defining equations are preserved. This avoids duplicating geometry, candidate
search or evaluation. The constrained root proposition retains the same domain
in every closed child, including overlapping boundaries.

The independent example proves both computed improvement and an actual root
without search soundness. Pole, infeasibility, backend and exhaustion controls
retain unknown. This remains finite search, not convergence or infeasibility
analysis. A useful next assessment is whether a work-budget contract is needed
before larger searches: depth bounds a potentially exponential tree and does not
bound expression evaluation cost. No broader search or representation change is
needed for this increment.

## Domain and search consolidation (2026-11-07)

The current #46–#58 chain has three distinct contracts. `DomainBounds.classify`
answers membership in a supplied/inferred partial domain; a yes promises a value,
not a zero. Exact singleton evaluation is complete at rational points, while an
unavailable range for a nonsingleton box does not imply undefinedness. Finally,
search establishes existence of a zero through a defined continuous path and an
explicit external region. These distinctions must survive any future unification.

The fresh `tests/DomainSearchIntegration.lean` compares the first two independent
analyses for every generated affine reciprocal sum: singleton evaluator success
is equivalent to `affineGuardsHold` at the same rational coordinates. Its concrete
`1/x + 1/y` client proves the exact zero set directly from partial value semantics,
then checks an exact point, an undefined pole, an unavailable whole-box range,
and successful restricted subdivision. Removing the full zero set through an
extra external condition leaves no restricted root despite the weaker region's
positive certificate. This is a cross-layer regression, not a new evaluator API.

Remaining conceptual gaps are substantive:

- Generated reciprocal sums form a useful restricted language, not recursive
  uncertain-input domain inference for arbitrary expressions. The earlier shared
  environment prototype has not silently become the production representation.
- Closed affine region conjunctions do not encode arbitrary holes, strict regions
  or disjunctions. An external domain cannot be omitted merely because the
  arithmetic has a certified path.
- Bounded search is a consumer of these certificates, not a general numerical
  domain representation or a completeness theorem. Subdivision retains unknown;
  a separate evaluation-cost contract would be required for a work budget.
- Source-equation access/comparison remains incomplete. These integration results
  do not close the concordance's obligations for actual thesis proofs.

The shared refinement extraction removes one potential duplication. There is no
justification yet for merging point-domain, affine-guard and range interfaces:
their different completeness scopes are useful, and the new agreement theorem
checks their overlap without requiring a migration. A high-value next step is to
select one precise arithmetic/domain theorem from the existing concordance and
close its source/specification obligation when readable evidence is supplied.
Until then, prefer targeted semantic regressions or a measured work-budget need
over further graph-specific search APIs.

Review risk is mainly branch integration: #44/#45 remain independent; the #45 core
was reused in #47 without all of its fixture/docs. The refreshed review guide
records this explicitly. This review does not merge, rebase, retarget or claim a
combined build of those independent trees.


<!-- Historical material from PR #44; original milestone claims and validation follow unchanged. -->

### Guard-provided cancellation (after #43)

The bounded removable case now has an exact semantic rewrite: the active strict
guard proves g-q nonzero, allowing its self-quotient to become one while retaining
the guard and false branch. Bidirectional ConditionalValue equivalence preserves
partiality at every coordinate, including undefined guards and false-branch
poles. A reusable proof transport connects explicitly equivalent expressions to
the existing conditional cover/domain evaluator; no replacement evaluator or
rewrite-discovery framework is needed.

The fresh client obtains a computed successful cover for the original relation
through that equivalence, preserving an external coordinate hole, and compares
against the independent direct semantic proof and prior unknown outcome. This
addresses a bounded precision issue without weakening the unbounded-range
impossibility results. Automatic matching and broader guarded rewrites remain
separate choices; there is no reason to add them before reviewing this rule's
exact syntax and partial-domain contract.


<!-- Historical material from PR #45; original milestone claims and validation follow unchanged. -->

## Post-merge numerical domain bridge (2026-11-07)

The authorized stack through #43 is on `main` at
`8ce2199f6d2d72c0c47269d02b8e1f1aa8cde7f0`. This increment starts there and does not
include or depend on #44, which remains under review. Rather than extend syntax,
`NonzeroDomains` links numerical containment to definite/possible partial-domain
evidence. The pole example connects it to existing expression semantics while
retaining unknown range enclosure. This separates a missing domain capability
from the proven finite-range representation limit. The next substantive gap is
an executable domain descriptor and its compositional integration, not a claim
that these real predicates already constitute such an interpreter.
