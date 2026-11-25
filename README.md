Original project sources are licensed under MIT by John Funge; dependencies retain their own licenses. See [migration provenance](MIGRATION.md).

# generalized-interval-arithmetic

This project's central purpose is proving properties of **Generalized Interval
Arithmetic**: arithmetic enclosure, partial domains, dependency, continuity and
covers. Conservative graphing and relgraph's C library are current applications
and initial comparison targets. They do not define the general mathematical scope.
The [scope and interface review](SCOPE.md) distinguishes reusable foundations from
restricted interpreters and graphing applications, including real coupling still
present in imports and module organization.

Run commands from this repository root. Building gia does not require relgraph
or private graphing sources. Pinned implementation references may require access;
they are not dependencies. Relgraph's application/library build has no dependency
on gia, and no hosted CI is introduced by this migration.

The runtime goal is provably correct interval arithmetic using hardware floating
point. Current exact-rational results are foundations, not completion of that goal.
The [hardware-backed addition and subtraction](HARDWARE_ADDITION.md) have compiled
Lean demos and conditional enclosure proofs. The guide also prioritizes the
remaining C operations for this path. The [hardware multiplier](HARDWARE_MULTIPLICATION.md) now assembles the four
rounded corners under the approved finite min/max contract and has a conditional
enclosure proof. [Guarded hardware division](HARDWARE_DIVISION.md) reuses that
assembly and proves denominator nonzero as well as quotient enclosure.
[Directed hardware square root](HARDWARE_SQUARE_ROOT.md) adds bounds for defined
roots on nonnegative and mixed-domain intervals.
[Hardware sine on [-1, 1]](HARDWARE_SINE.md) composes directed arithmetic with
proved fifth-degree Taylor bounds, monotone endpoints and odd symmetry; it neither
trusts libm sine nor claims correct rounding.
[Certified pi and finite period reduction](HARDWARE_SINE_REDUCTION.md) extend it
to intervals near a bounded set of whole-period shifts, with explicit unknown
when no reduced interval fits.
[Hardware cosine and quadrant coverage](HARDWARE_COSINE_QUADRANTS.md) add a cosine
kernel and a closed sine cover on [-4,4], including intervals crossing extrema.
The [architecture assessment](HARDWARE_FLOAT_PLAN.md)
records broader choices; it predates this explicitly authorized small milestone.

[Global sine fallback](HARDWARE_SINE_GLOBAL.md) composes period reduction with
that quadrant kernel and supplies the proved [-1,1] bound when refinement fails.
It handles arbitrary finite input magnitudes conservatively, without claiming
accurate full-range reduction.

[Bounded automatic reduction](HARDWARE_SINE_DYADIC.md) uses certified dyadic
period shifts to improve narrow-input bounds near magnitude one million, with
no trusted quotient-to-integer conversion or new floating-point assumptions.

[Certified split pi](HARDWARE_SINE_SPLIT_PI.md) keeps small reduction corrections
separate until coarse cancellation finishes, improving tested narrow-input
bounds near magnitude one trillion under the same floating-point contract.

[Pure binary64 decoding](BINARY64.md) proves exact rational values and pi/tail
enclosures for the four raw constant words. Native Float bit conversions remain
trusted/empirical; no rational arithmetic is added to the hardware runtime.

[Shared partial-real semantics](PARTIAL_REAL_ARITHMETIC.md) centralizes the proof-side
operation meanings and division guard while preserving both public operation
inductives, their reductions and all existing evaluator algorithms.

[Directed scheduling equivalence](DIRECTED_SCHEDULING.md) proves that independent
Down/Up requests reassemble to the scalar result under the same per-request
denotation, including failures. It is a proof model, not production batching.

[Split quotient semantics](SPLIT_QUOTIENT.md) preserves both sides of a pole in
proof-side real ray enclosures, with exact scalar reciprocal images distinguished
from arbitrary expression enclosures. It does not change a runtime evaluator.

[Integer residue certificates](INTEGER_RESIDUE.md) retain discrete information
alongside real enclosures. This proof foundation excludes closed windows
using certified integer provenance; it does not change runtime or ASTs.

[Smaller-angle refinement](HARDWARE_SINE_HALVING.md) reconstructs sine/cosine
with proved double-angle identities and intersects with the previous result,
improving tested narrow-input accuracy without widening existing enclosures.

[Hardware affine forms](HARDWARE_AFFINE.md) connect the shared-parameter linear
model to directed binary64 addition, subtraction and scalar multiplication,
retaining endpoint rounding uncertainty and useful shared-parameter cancellation.

[Shared-parameter hardware multiplication](HARDWARE_AFFINE_PRODUCT.md) encloses
the quadratic residual and returns a composable affine form. It tightens
`t(1−t)` from ordinary `[0,1]` to `[0,1/4]`, without a universal precision claim.

[One-variable hardware evaluation](HARDWARE_EVALUATOR.md) runs ordinary and affine
tracks through one traversal, intersects successful bounds, and preserves a
surviving track while exposing contradictory outputs explicitly.

[Convex and concave endpoint chords](ENDPOINT_CHORDS.md) formalize the finite
closed-domain chord bounds, exact affine optimality and Tupper’s cubing example.
Outward-certified endpoint soundness is kept separate from optimality.

[Guarded hardware quotient composition](HARDWARE_GUARDED_QUOTIENT.md) reuses those
polynomial blocks and adds partial division and interval arithmetic around them.
Successful bounds certify defined values; zero-crossing guards remain unknown.

[Finite-domain tangent bounds](TANGENT_BOUNDS.md) complement the chords with
concave upper tangents and convex lower tangents under explicit derivative
certificates, without claiming pointwise optimality across contact choices.

[Unary affine propagation](AFFINE_UNARY.md) composes certified chord/tangent
lines with uncertain affine inputs, preserves ordinary fallback and explicit
domains, and demonstrates nested squaring. This is a portable theorem/reference
layer; hardware unary integration remains future work.

## Start here

| Question | Read |
| --- | --- |
| How general are the interfaces? | [Foundations versus applications](SCOPE.md) |
| What is proved, and under which semantics? | [Scope below](#scope), then [generalized intervals and domains](GENERALIZED_INTERVALS.md) |
| How do I reproduce the checks? | [Pinned setup](#reproducible-setup), then run `./check.sh`; see [audit policy](AUDIT_POLICY.md) |
| Where are end-to-end examples? | [Basic operations and box exclusion](tests/BasicIntervalOps.lean), then [constrained subdivision](tests/AffineRegionSubdivision.lean) |
| What is the initial floating-point target? | [Tupper-first gap map](FLOATING_POINT_ROADMAP.md): source assumptions, existing proofs and missing constructions |
| Which C operations have corresponding mathematics? | [Operation coverage ledger](OPERATION_COVERAGE.md) |
| How does this relate to Tupper? | [Thesis concordance](THESIS_CONCORDANCE.md): verified section links, narrower results and missing topics |
| What is incomplete or under review? | [Integration assessment](INTEGRATION_ASSESSMENT.md), [review stack](REVIEW_STACK.md), and [recorded validation](VALIDATION.md) |

Documentation is updated with each milestone: purpose, semantic contracts,
assumptions, limits, executable examples and relevant thesis sections. Historical
validation records describe the versions actually checked; current scope pages
explain today's interfaces. The topic documents below are the reference map,
not a required reading sequence.

### Reading order and review status

Start with `Intervals` / `IntervalOps` for finite arithmetic and `PartialEnclosures` /
`UniversalDomains` for generic partial semantics. `Intervals` still also contains
graphing examples; `Evaluator` is a two-variable client, not the general core. Read `LinearIntervals`, `PartialEnclosures` and
`DomainEvaluator` for shared parameters and domain contracts. Then follow either
`GuardedEvaluator` / `ConditionalEvaluator` for composition, or `Presence` /
`CellCertification` for consumers. The linked topic notes explain the contracts;
`tests/` contains independent integration clients.

The published gia baseline is `1f67388`, imported from relgraph main `7fd4b39`
through PR #73. Hardware square root, originating in relgraph PR #74
(`f7cfea8`), merged as gia #1 (`a6cb4c8`). The positive-domain sine milestone
merged as gia #2 (`bb937fa`). Signed monotone endpoint bounds on [-1, 1] merged
as gia #3 (`9ea7d9d`).
Certified pi and finite whole-period reduction merged as gia #4 (`eef2d07`).
Cosine and quadrant coverage merged as GIA #5 (`d1caaaf`); composed period
reduction and global fallback merged as GIA #6 (`0192ef2`); bounded dyadic
reduction merged as GIA #7 (`1ba0723`); split pi and deferred corrections
merged as GIA #8 (`278fbe0`); smaller-angle reconstruction merged as GIA #9
(`b3ff033`); hardware affine addition/subtraction/scaling merged as GIA #10
(`ce041d2`); shared-parameter multiplication merged as GIA #11 (`8906100`).
This local milestone adds dual-track polynomial evaluation, retaining the same
adapter trust boundary and MIT notices.
The earlier [review stack](REVIEW_STACK.md), [merge plan](MERGE_PLAN.md) and
validation sections are historical snapshots, not current pending-PR lists.
The [public-operation coverage ledger](OPERATION_COVERAGE.md) distinguishes
merged mathematical proofs, evaluator integration, domain limits and gaps.
The [basic interval operations](BASIC_OPERATIONS.md) were merged in PR #69.
[Monotone endpoint bounds and floor/ceiling](MONOTONE_INTEGER_BOUNDS.md) and the
first hardware-addition milestone were merged in PR #70.
The coverage ledger distinguishes current review work from merged milestones.

The core supports enclosure, partial-domain and conditional semantics, finite
covers, and conservative presence/absence certificates. It does not provide
complete domain inference, arbitrary constraint solving, unbounded finite-cover
ranges, or verified IEEE 754 implementation behavior. General evaluation failure
and unavailable ranges remain distinct from undefinedness. The completeness-backed exception is exact rational singleton
evaluation in `PointDomains`; see the [concordance assumptions](THESIS_CONCORDANCE.md#assumptions-and-interpretation-rules).

The Lake package is `generalized_interval_arithmetic`; declarations use the
`GeneralizedIntervalArithmetic` namespace. Modules describe their contents:
`Intervals`, `IntervalOps`, `BasicIntervalOps`, `MonotoneIntegerBounds`,
`RoundedAddition`, `Evaluator`, `EvaluatorRounding`, `EvaluatorExamples`,
`Presence`, `ExpressionContinuity`, `PresenceExamples`, `PresenceChecker`,
`PresenceCheckerExamples`, `SegmentSearch`, `SegmentSearchExamples`,
`Subdivision`, `SubdivisionExamples`, `LinearIntervals`, `PartialEnclosures`,
`GeneralizedExamples`, `LinearMultiplication`, `MultiplicationExamples`,
`LinearEvaluator`, `LinearEvaluatorExamples`, `LinearDivision`, `DivisionExamples`,
`DomainEvaluator`, `DomainEvaluatorExamples`, `GuardedEvaluator`, and
`GuardedEvaluatorExamples`, `PiecewiseSelection`, `PiecewiseExamples`, `DomainQueries`, `NonzeroDomains`, `QuotientDomains`, `PointDomains`, `AffineDomainGuards`, `AffineSegmentDomains`, `AffineRegions`, `AffineRegionSearch`, `AffineRegionSubdivision`,
`ConditionalEvaluator`, `ConditionalExamples`, `ConditionalArithmetic`, and
`ConditionalArithmeticExamples`, `ParameterRestriction`, and
`ParameterRestrictionExamples`, `SemanticContinuity`, and
`SemanticContinuityExamples`, `CellContinuity`, `CellContinuityExamples`,
`ConditionalContinuity`, `ConditionalContinuityExamples`, `FiniteLinearCovers`,
`FiniteLinearCoverExamples`, `ConditionalCovers`, `ConditionalCoverExamples`,
`CoverPresence`, `CoverPresenceExamples`, `CoverCoalescing`, and
`CoverCoalescingExamples`, `CoverRestriction`, `CoverRestrictionExamples`, and
`CellCertification`, `CellCoverage`, `AdaptiveCellCertification`, `CoverArithmetic`, `ThresholdCertification`, `GuardedSimplification`, `UniversalDomains`, and
`SquareRootDomains`.

The [presence theorems](PRESENCE.md) complement empty-box classification with
defined-root existence along a certified continuous segment. For supported
expressions, successful whole-box evaluation proves the required continuity and
definedness, including guarded division.
An executable segment checker combines these results into sound `empty`,
`present`, or `unknown` decisions for a supplied pair of endpoints.
The [finite segment search](SEGMENT_SEARCH.md) searches supplied candidates or
uses eight automatically generated center-to-boundary segments, retaining the
same soundness guarantees and explicit unknown outcome.
[Bounded subdivision](SUBDIVISION.md) refines inconclusive boxes with proved
coverage and conservative aggregation of child results.

The [generalized interval milestone](GENERALIZED_INTERVALS.md) adds rational
linear bounds over a shared parameter, sound addition/subtraction and hull
conversion, and separate semantic contracts for partial-function domains.

[Linear multiplication](LINEAR_MULTIPLICATION.md) adds a certified quadratic-to-linear
product enclosure and preserves explicit domain information. The
[review guide](REVIEW_STACK.md) explains the incremental PR stack.

The [enforced axiom audit](AUDIT_POLICY.md) is a default Lean build target and
rejects transitive dependencies outside the explicit allowlist.

The [linear expression interpreter](LINEAR_EVALUATOR.md) bridges the polynomial
fragment to the existing partial real semantics, preserving shared parameters
and treating division as unsupported/unknown.

[Guarded linear division](LINEAR_DIVISION.md) adds reciprocal and quotient
enclosures with explicit nonzero guards and preserved operand domains.

The [domain-local interpreter contracts](DOMAIN_EVALUATOR.md) accept partial
coordinate relations or enclosure premises restricted to a supplied domain.

The [integrated guarded interpreter](GUARDED_EVALUATOR.md) composes division
with the arithmetic and domain-local contracts, with locally proved definedness
and exact compatibility on prior successful polynomial interpretations.

[Piecewise selection](PIECEWISE_SELECTION.md) composes branch value/domain
contracts under certified or unknown decisions, with explicit discontinuity
controls and no implied continuity certificate.

[Conditional trees](CONDITIONAL_EVALUATOR.md) add partial arithmetic guards,
nested branch selection, and proved independence from inactive branches when
a decision is certified, while unresolved cases remain conservative.

[Arithmetic composition of conditional trees](CONDITIONAL_ARITHMETIC.md) proves
exact preservation of partial values and domains when distributing arithmetic
through branches, then reuses the existing enclosure evaluator.

## scope

The source is a small foundation for the interval enclosure and conservative
graphing ideas in Jeffrey Allen Tupper's *Graphing Equations with Generalized
Interval Arithmetic* ([thesis](https://www.dgp.toronto.edu/~mooncake/thesis.pdf)).
It covers a small part of the chapter-2/3 foundations, not a transcription of a numbered thesis theorem
or a claim to have formalized either chapter. The
[thesis concordance](THESIS_CONCORDANCE.md) maps verified section references
to current declarations and distinguishes restricted coverage from missing work.

`Intervals.lean` defines finite, ordered rational intervals, interpreted as
closed subsets of mathlib's real numbers. It proves:

- addition encloses every sum of members;
- subtraction encloses every difference, with the second pair of endpoints swapped;
- strict exclusion of zero makes an `empty` classification sound;
- a uniform enclosure over a rectangle justifies excluding all zeros there;
- `[1/2, 1] × [-1/4, 1/4]` is empty for `x + y = 0`, using the enclosure `[1/4, 5/4]`;
- a zero boundary remains `unknown`, and `unknown` does not establish existence.

The general pixel theorem explicitly assumes an enclosure for **every** real point
of the rectangle. The example discharges that assumption with the addition
theorem. Functions in that theorem are total real functions; partial-function
domain handling is outside this model. Continuity is unnecessary for this
one-sided exclusion argument.

There are no new axioms or placeholder proofs. `Audit.lean` prints the actual axiom
dependencies after building. Standard Lean/mathlib foundations are trusted, as
are the Lean kernel, compiler/runtime and the installed toolchain. This is not
an independently bootstrapped proof checker.

## conditional IEEE 754 rounding extension

`RoundedAddition.lean` adds a deliberately small conditional theorem, following
John's clarification that rounding modes may be assumed. The reference is
[IEEE 754-2019, Standard for Floating-Point Arithmetic](https://standards.ieee.org/ieee/754/6210/).
The intended directions are toward negative infinity for the lower bound and
toward positive infinity for the upper bound; these directions are also described
in the vendor's [IEEE arithmetic guide](https://docs.oracle.com/cd/E19957-01/806-3568/ncg_math.html).

For input intervals `I` and `J`, the caller supplies `down, up : ℚ → ℚ` and exactly
two local contracts:

```text
down (I.lo + J.lo) ≤ I.lo + J.lo
I.hi + J.hi ≤ up (I.hi + J.hi)
```

**Assumed:** these inequalities hold for the two returned finite endpoint values.
The functions stand for the numerical effect of the rounding operations at those
calls; they are not implementations of IEEE operations. No global contract on
all rational inputs is required.

**Proved:** the resulting endpoints are ordered, their interval contains `x + y`
for every real `x ∈ I` and `y ∈ J`, and an `empty` classification of that rounded
interval excludes every solution of `x + y = 0` in the input rectangle. The
rounding contracts are hypotheses in the theorem types, not added axioms.

The intended application format is IEEE 754 binary64, with 53-bit significand
precision (see the [double-format reference](https://docs.oracle.com/cd/E37069_01/html/E39019/z4000ac019269.html)).
The theorem itself is format-independent: it does not encode binary64 or check
representability, correct rounding, or optimality of the supplied endpoints.
`halfway_candidate_bounds` checks the strict rational inequalities
`1 < 1 + 2^-53 < 1 + 2^-52`; it does not claim that an FP implementation returns
the two outside values.

| case | scope |
| --- | --- |
| finite values, including negative and subnormal values | their exact rational values can be used; the two rounding contracts still must be supplied |
| exact endpoint results | non-strict contracts permit equality |
| signed zero | both signs have rational value zero; sign behavior is not modeled |
| NaN, infinities, overflow producing infinity | not represented by this finite rational interface |
| underflow behavior, exception flags, FP environment | not proved; no extra behavior is assumed beyond the two local contracts |

Model investigation found opaque `Float` arithmetic in the pinned
[Lean 4.19.0 source](https://github.com/leanprover/lean4/blob/v4.19.0/src/Init/Data/Float.lean).
The pinned mathlib has rational floor/ceiling machinery, but no binary64 model was
found in the inspected modules. [Lean 4.33.0 introduced a `Float.Model`](https://lean-lang.org/doc/reference/latest/releases/v4.33.0/).
No model, toolchain upgrade, or extra dependency was introduced: this extension
uses only the requested enclosure assumptions. A fuller IEEE formalization or
implementation link would be a separate scope decision to discuss first.

## reproducible setup

The compositional evaluator provides guarded division, a
shared exact/conditional-rounding enclosure proof, and zero-exclusion examples.
See [the evaluator notes](EVALUATOR.md) for its partial semantics, explicit
contracts, examples, and limitations. It is included in the Lean project build below.

- Lean: `leanprover/lean4:v4.19.0` (see `lean-toolchain`).
- mathlib: `c44e0c8ee63ca166450922a373c7409c5d26b00b` (v4.19.0).
- `lake-manifest.json` locks transitive dependency revisions.

With the pinned Lean toolchain on `PATH`:

```sh
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
lake build
lake env lean Audit.lean
```

The first build may compile mathlib dependencies from source. On a network that
permits mathlib's cache service, `lake exe cache get` can fetch precompiled objects
before the build. Do not change network policy or bypass a proxy to reach it.

The cloud environment has installed the official Lean release in
`/workspace/lean-tools/lean-4.19.0-linux`, outside the repository. For this instance:

```sh
export PATH=/workspace/lean-tools/lean-4.19.0-linux/bin:$PATH
```

The downloaded `lean-4.19.0-linux.tar.zst` had SHA-256
`6fe3ce97a58f44e2b3567d455b994eacec5bfe9ae7774f2a573444480ba813fe`.
This records the observed artifact, not an independent signature verification.
The setup does not assume global elan installation or modify shell startup files.

## limits and next steps

This does **not** verify binary64 rounding, NaNs, infinities, signed zero, MPFR,
the C sources, the renderer, screen-coordinate conversion, or a release artifact.
Rational endpoints and arithmetic here are exact. The rounding extension proves
enclosure conditionally on its two explicit contracts; it does not discharge
those contracts for an FP implementation. No performance or optimal-enclosure
claim is made.

Keep future milestones separate from v1.0: first establish a thesis chapter and
definition concordance; then extend exact enclosures and domain semantics; then
specify outward floating-point rounding and prove a refinement to the real model;
only afterward connect implementation operations and prove optimization
preservation. These are future proof obligations, not consequences of this formalization.

See `VALIDATION.md` for the actual cloud run and remaining setup limitations.

## integrated review and validation

Start with [the integration and thesis assessment](INTEGRATION_ASSESSMENT.md) for
the current module boundaries, missing foundations, stack risks, and next-step
recommendation. Run `./check.sh` here with the pinned Lean/Lake and Python 3.11+
on PATH for the build, fresh axiom audit, coverage controls, and end-to-end tests.

[Parameter restriction and coverage](PARAMETER_RESTRICTION.md) now supply exact
affine reparameterization, transported partial domains, and universal claims
recombined through a certified finite closed cover.

[Semantic continuity](SEMANTIC_CONTINUITY.md) connects defined arithmetic and
continuous coordinates to relative continuity, including guarded linear
evaluation and restricted cells, without treating domain holes or conditional
jumps as whole-interval continuity certificates.

[Closed-cell continuity composition](CELL_CONTINUITY.md) now glues restrictions
of a common function over a proved finite closed cover, with explicit agreement
requirements for local representatives and separate definedness obligations.

[Conditional continuity certificates](CONDITIONAL_CONTINUITY.md) give a sufficient
matching-boundary rule for parameter-threshold guards, retaining active-branch
definedness and permitting a continuous extension of an inactive boundary hole.

[Finite linear covers](FINITE_LINEAR_COVERS.md) preserve separated ranges through
branch selection and guarded reciprocation, with enclosure distinct from
definedness and continuity.

[Conditional covers with domains](CONDITIONAL_COVERS.md) integrate the existing
lazy conditional interpreter with finite ranges and preserve partial-domain
guarantees through successful componentwise reciprocation.

[Domain-certified cover presence](COVER_PRESENCE.md) combines finite ranges,
whole-path definite definedness, and independently proved continuity to certify
an actual root, with a punctured-domain counterexample.

[Sound cover coalescing](COVER_COALESCING.md) provides range inclusion, a scalar
interface bridge, and an optional proved output-size limit. It preserves domain
guarantees while making possible precision loss explicit.

[Finite-cover parameter restriction](COVER_RESTRICTION.md) reuses exact cell
reparameterization and pulled-back domains, with multivalued, coalescing-order,
degenerate-hole, and conditional-reevaluation controls.

The fresh-process fixtures in [tests/Integration.lean](tests/Integration.lean),
[tests/CoverPipeline.lean](tests/CoverPipeline.lean), and
[tests/CellCertificates.lean](tests/CellCertificates.lean) exercise core APIs without
milestone example imports. `./check.sh` enforces their registry, transitive import
independence under the `*Examples` convention, and separate namespace audits.
Historical stack snapshots are retained in [REVIEW_STACK.md](REVIEW_STACK.md).

[Fuelled cell certification](CELL_CERTIFICATION.md) checks a supplied cell list
using the existing guarded evaluator. The proved budget counts evaluator calls;
a supplied coverage proof or the conservative automatic coverage front end, plus
continuous enclosed coordinates, turns successful local checks into an arithmetic
definedness/continuity certificate. The independent
[CellCertificates fixture](tests/CellCertificates.lean) tests exhaustion, early
failure, missing coverage, and an actual-root pipeline.

`DomainQueries` executes three-way queries against existing decidable domain
predicates, with domain-only existence/absence certificates and a rational
partial-expression client. See the [query scope](GENERALIZED_INTERVALS.md#executable-queries-of-certified-domains).

`QuotientDomains` automatically constructs rational-parameter domain descriptions
for one outer quotient, reusing guarded child evaluation and the nonzero-domain
certificates. See [automatic quotient-domain scope](GENERALIZED_INTERVALS.md#automatic-quotient-domain-descriptions).

`PointDomains` proves completeness of the existing exact evaluator at rational
singleton inputs and reuses it for recursive pointwise domain inference. The
[exact-point scope](GENERALIZED_INTERVALS.md#recursive-exact-point-domains) is
strictly narrower than general interval evaluation.

The [uncertain-input feasibility assessment](INTEGRATION_ASSESSMENT.md#feasibility-of-recursive-uncertain-input-domains-2026-11-07)
records kernel-checked shared-witness and unbounded-range controls before further
recursive domain inference. It adds tests, not another analyzer.

The [representation comparison](INTEGRATION_ASSESSMENT.md#representation-comparison-and-isolated-prototype-2026-11-07)
includes a test-only shared-environment/optional-range prototype. It preserves
current production APIs and separates domain knowledge from range availability.

`AffineDomainGuards` is a small certified family of reciprocal sums with finite
nonzero affine guards over a shared two-coordinate environment. It preserves
external domains and reuses the existing query API; see the
[guard scope](GENERALIZED_INTERVALS.md#shared-environment-affine-guards).

`AffineSegmentDomains` connects the shared affine guards to the existing presence
checker: a safe segment can certify a zero even when an off-segment pole blocks
whole-box evaluation. See [segment scope](GENERALIZED_INTERVALS.md#affine-domain-certificates-along-segments).

The [restricted segment-domain completeness result](GENERALIZED_INTERVALS.md#completeness-of-the-restricted-segment-domain-test)
now distinguishes failure of `affineSegmentSafe` (an actual arithmetic hole
somewhere on that segment) from an inconclusive numerical presence check.

The [external-domain bridge](GENERALIZED_INTERVALS.md#presence-and-absence-under-external-domain-restrictions)
transports certified presence using a caller-proved whole-path restriction;
proved absence transports to any restriction. Endpoint membership alone does not
justify restricted presence.

`AffineRegions` [checks finite closed affine constraints](GENERALIZED_INTERVALS.md#executable-external-regions-from-affine-constraints)
on a supplied segment and discharges the external-domain presence premise for
that class. Unknown does not imply infeasibility, and path exclusion does not
imply box emptiness.

`AffineRegionSearch` [searches existing segment candidates within affine regions](GENERALIZED_INTERVALS.md#finite-segment-search-inside-affine-regions),
including the established eight-candidate box policy. Failed searches stay unknown;
only the existing whole-box arithmetic test can certify empty.

`AffineRegionSubdivision` [reuses bounded subdivision for this constrained search](GENERALIZED_INTERVALS.md#bounded-subdivision-inside-affine-regions).
It preserves the same region in each closed child and can recover roots missed
by the parent candidate policy. Exhaustion remains unknown; there is no general
root-search completeness or convergence claim.

The [domain/search consolidation](INTEGRATION_ASSESSMENT.md#domain-and-search-consolidation-2026-11-07)
and [independent integration fixture](tests/DomainSearchIntegration.lean) compare
point-domain inference, affine guards and constrained subdivision. They distinguish
undefined points, unavailable box ranges and additional external holes. The
[review guide](REVIEW_STACK.md#current-unmerged-integration-snapshot-2026-11-07)
records the former unmerged chain and independent branch overlap, now integrated.

The [Lean integration plan](MERGE_PLAN.md) records exact observed heads, dry-run
conflicts, targeted cross-branch checks, and a proposed dependency-preserving
sequence. That rehearsal was subsequently validated and merged as recorded above;
the plan itself remains a historical snapshot, not current merge authorization.

The first [PDF-grounded affine representation correspondence](GENERALIZED_INTERVALS.md#finite-rational-correspondence-with-thesis-coefficient-bounds)
connects thesis coefficient bounds to the existing endpoint representation,
with exact round trips and a non-collapsing equivalence for finite rational
coefficients. Its [fresh evaluator controls](tests/AffineCorrespondence.lean)
include the source's cancellation comparison and explicit scope counterexamples.

The [constant-interval embedding](GENERALIZED_INTERVALS.md#constant-interval-embedding-from-thesis-section-294)
continues with thesis §2.9.4: injectivity and exact preservation of finite rational
addition, subtraction and multiplication, including a success-conditioned
interpreter correspondence. [Independent controls](tests/ConstantEmbedding.lean)
state the limits of the homomorphism comparison.

The chapter-2 quadratic bridge is documented in
[Quadratic bounds and fixed-chord corrections](GENERALIZED_INTERVALS.md#quadratic-bounds-and-fixed-chord-corrections),
with independent controls in [QuadraticChord](tests/QuadraticChord.lean).
It proves sharp corrections for a fixed chord, not general affine optimality.

The [two-parameter affine validity test](GENERALIZED_INTERVALS.md#two-independent-affine-parameters)
provides a complete four-corner non-collapse criterion for finite rational
bounds on the unit square, with [independent semantic controls](tests/TwoParameterBounds.lean).

For the chapter-2 domain contract, read
[Universal input-domain semantics](GENERALIZED_INTERVALS.md#universal-input-domain-semantics)
and [UniversalDomains.lean](UniversalDomains.lean). This layer distinguishes
“one represented input is defined” from “every represented input is defined,”
connects to guarded evaluation, and documents the nonempty-input condition
needed to recover the older existential contract. Its
[counterexamples and integration fixture](tests/UniversalDomains.lean) are run
by `./check.sh`; its exact logical domain envelope is not an executable solver.

A concrete application of that contract is
[square root with domain tracking](GENERALIZED_INTERVALS.md#square-root-with-domain-tracking),
following the paper's three-branch algorithm with exact-real endpoints. The
[regressions](tests/SquareRootDomains.lean) include the thesis examples and
document a loose source example and its difference from the precise paper rule.

Before extending generic continuity-property tracking, see the
[property-composition source review](THESIS_CONCORDANCE.md#property-tracking-specification-obstruction).
Its registered Lean counterexample distinguishes the valid sufficient rule
from the thesis's literal printed reverse direction; an intended-specification
decision is still needed.

Numerical nonzero-domain certificates (`NonzeroDomains`) refine existing partial
relations and derive quotient domain evidence independently of quotient range
bounds. See the [domain certificate scope](GENERALIZED_INTERVALS.md#numerical-nonzero-domain-certificates).

The integration rehearsal recorded in [MERGE_PLAN.md](MERGE_PLAN.md) was merged
with the exact validated tree in `d464677`; its original receipts remain historical.

[Local residue inference foundation](RESIDUE_INFERENCE.md) describes a narrow
proof-side syntax and conditional provenance inference, separate from runtime.

[Pointwise affine conjunction](AFFINE_CONJUNCTION.md) retains ordinary and affine
constraints together for square and affine addition, as a proof-side reference.

Proof-side guarded division: [two-corner exact extrema](TWO_CORNER_DIVISION.md)
and a conditional assembly bridge, with explicit availability/width limits.

The [Chapter 2 checklist](CHAPTER2_CHECKLIST.md) tracks source-numbered foundations
and open obligations. [Finite affine storage and evaluation](FINITE_AFFINE_DEMOTION.md)
is a restricted §2.10 proof-side certificate/evaluation layer.

[Observed-outcome division refinement](TWO_CORNER_REFINEMENT.md) proves a
conditional assembly comparison, without changing runtime or rounding contracts.

[Exact image hulls](EXACT_IMAGE_HULL.md) separate actual partial output sets,
least closed real enclosures and conditional outward addition results.

[Executable Word two-corner reference](WORD_TWO_CORNER.md) validates every endpoint
before dispatch and proves standalone enclosure separately from old-result refinement.
It does not replace the native four-corner path.

The [proved binary64 key selector](KEY_TWO_CORNER.md) has exact ordered-request
and explicit-trace equivalence with the rational reference, with standalone
enclosure and conditional refinement transported. Its opt-in native experiment
compares the actual proved route, rational reference and four-corner baseline;
no default runtime path is changed. The [foundation record](BINARY64_KEY.md)
preserves the earlier checkpoint and proof roadmap.

[Finite three-valued strict comparison](STRICT_COMPARISON.md) proves the exact
Boolean outcomes for independent finite real interval operands, with explicit
mixed-case witnesses and a correlated-input counterexample. It is a narrow
Chapter 2 foundation, independent of the exact image-hull work.

[Finite Boolean composition](BOOLEAN_COMPOSITION.md) extends the existing
three-valued descriptions with exact independent not/and/or images and sound
common-witness enclosures. Correlation controls distinguish those guarantees;
this remains a proof-side Chapter 2 foundation.

The [Chapter 2 completion criteria](CHAPTER2_COMPLETION.md) separates proved
finite models, library foundations and unresolved source obligations, with a
dependency-ordered plan. [Same-parameter domain constraints](DOMAIN_CONSTRAINTS.md)
connect finite conjunction/classification weakening to the existing universal
domain semantics; full numeric domain demotion remains open.

## Finite logical and numeric-domain interfaces

The [finite comparison package](FINITE_COMPARISONS.md) and
[domain projections](DOMAIN_PROJECTIONS.md) cover optimistic/pessimistic
projections, exact independent finite comparison images, threshold/nonzero
classifiers and same-witness partial sqrt/division domain bridges. Numeric
re-encoding preserves classifications under explicit whole-image and transport
premises. Touching/equal-singleton, correlation, holes, nonmonotone predicates
and unsafe re-encoding controls are kernel-checked. Source: Tupper §2.7.2
(printed p.24 / PDF p.40) and §2.11 (printed pp.34–36 / PDF pp.50–52).
Exceptional endpoints, general descriptor generation and full family demotion
remain outside this milestone; Chapter 2 is not complete. No native or FP
contract change is made.


## Mathematical representations, bounds and exceptions

The representation unit adds [extended actual-real-image hulls](EXTENDED_IMAGE_HULL.md),
[source-scoped exceptional comparisons](EXCEPTIONAL_COMPARISONS.md) and
[arithmetic](EXCEPTIONAL_ARITHMETIC.md), [literal-infinity controls](EXCEPTIONAL_FAMILIES.md),
[signed divergence correspondence](INFINITY_STREAMS.md),
[integer promotion/demotion](NUMBER_PROMOTION.md), and
[finite-family extremal demotion](DISCRETE_DEMOTION.md).
The independent positive-infinitesimal leaf reuses pinned mathlib.
[Finite interval algebra](INTERVAL_ALGEBRA.md), [nonnegative cut arithmetic](CUT_ARITHMETIC.md),
[rational sequences/digits](SEQUENCE_AND_DIGIT_REPRESENTATIONS.md) and
[canonical continued-fraction conversion](CONTINUED_FRACTION_CONVERSION.md)
record their exact source correspondences and boundary controls.

These are mathematical proofs, not native deployment or a completion of Chapter 2.
Empty actual-real images, infinite bounds, literal infinity tags and lambda are
distinct. Mixed exceptional comparison directions, full source-carrier promotion,
unspecified arithmetic rows and arbitrary infinite coefficient reconstruction
remain open. Later family conversion and property-tracking units are not included.
No floating-point premise or hardware implementation changes.


## Families, sets and domain-compatible demotion

[Family demotion](FAMILY_DEMOTION.md) and its
[general partial-domain rule](GENERAL_FAMILY_DEMOTION.md) preserve shared witnesses
and separate enclosure from classification. Concrete instances cover
[linear equality and its source qualification](LINEAR_FAMILY_EQUALITY.md),
[multiple affine parameters](MULTI_AFFINE_FAMILIES.md),
[quadratic families](QUADRATIC_FAMILIES.md), and the
[finite promotion chain](FINITE_FAMILY_CHAIN.md).
[Interval sets](INTERVAL_SET_DENOTATION.md),
[set-valued extension](INTERVAL_SET_EXTENSION.md),
[coefficient variants](INTERVAL_COEFFICIENT_VARIANTS.md), and
[finite descriptions](FINITE_DESCRIPTIONS_AND_CUTS.md) retain their explicit
representation restrictions. [Descriptor demotion](DESCRIPTOR_DEMOTION.md) proves
a whole-set conversion and preserves external holes and original tags.

These results do not establish a universal finite family syntax, arbitrary bumpy
functions, or the full source exceptional algebra. Inclusion is not exactness;
projected range containment is not pointwise containment at a shared parameter.
Property tracking and expression accuracy remain separate. No native/default
change or new floating-point premise is included; Chapter 2 remains incomplete.


## Partial properties and accuracy: integrated scope

[Partial properties](PARTIAL_PROPERTIES.md), [finite-arity composition](FINITE_PROPERTIES.md)
and [tracking certificates](TRACKING_CERTIFICATES.md) prove exact strict
definedness and sufficient continuity/local-constancy transport on actual shared
tuples. The literal source weak-continuity implication remains refuted by the
constant and square masking controls; sufficient certificates are not silently
substituted for that source claim. Failure of a certificate remains inconclusive.

[Expression streams](EXPRESSION_STREAMS.md) prove eventual success, enclosure and
convergence for the existing finite rational arithmetic evaluator when its limit
has a strict semantic value. Endpoint containment is an additional premise for
a limit-value error certificate. The compiled proof-backed search example rejects
two initial stages and returns a certified interval; it is not a new native FP
backend, a rate bound, or an implementation of arbitrary real inputs.

The [consolidated source audit](CHAPTER2_SOURCE_AUDIT.md) is the current finish-line
map. Full source-carrier/exceptional promotion, the weak-tracking interpretation,
and general finite guard/piece representations remain substantive gaps.
Newer tagged conversion remains separate. Chapter 2 is not declared complete.

## Tagged family conversion preservation

[Tagged conversion](TAGGED_CONVERSION.md) proves exact composition of lifted
real-set converters while retaining literal negative infinity, positive infinity
and lambda separately. Sound empty-preserving converters give arbitrary-predicate
classification refinement and exact represented definedness bits. The real-hull
then integer-hull instance discharges these premises with existing proofs.
This is a derived semantic preservation theorem, not the full source F-to-R*
promotion, an exceptional operation table, or a native implementation. Those
concrete carrier/operation gaps remain in the [source audit](CHAPTER2_SOURCE_AUDIT.md).

## Literal finite-format enclosure

[Finite formats](FINITE_FORMAT.md) proves exact representation of the §2.5
printed p.18 coefficient formula for arbitrary radix at least two, positive
precision and ordered exponent bounds, with least finite in-range directed
enclosure. Its Word bridge requires separate format membership. The adjacent
digit presentation and IEEE identification remain open; no new FP premise or
implementation is introduced, and Chapter 2 remains incomplete.

## Coefficient/digit distinction

[Format digits](FORMAT_DIGITS.md) checks the §2.5 printed pp.18–19 displays:
exact digit-list correspondence, normalized magnitude bounds, literal
nonnegative reindexing and a minimum-exponent obstruction. A checked decimal
counterexample rules out unconditional equality of the displays. An explicitly
labeled external-sign / `b^A` coefficient repair is proved; the original model
is unchanged. Authorial intent, full normalization and IEEE identification remain
open. This refines the earlier “digit correspondence open” entry, not Chapter 2
completion or a new FP assumption.

## Repaired binary64 value correspondence

[Binary64 format bridge](BINARY64_FORMAT.md) proves the full iff between the
repaired `(2,53,-1022,1023)` family and successful finite `Binary64.decode`
values, including normal/subnormal cases and both signed zeros. Bounded exact
normalization and raw-word packing discharge the converse, and identify the
existing mathematical demotion target. This closes the repaired-family bridge
previously deferred above; the literal printed coefficient model is unchanged.
No native transport, exceptional rounding, new FP premise or chapter-completion
claim follows.

## Endpoint certificates and optimality

[Endpoint optimality](ENDPOINT_OPTIMALITY.md) proves that a sound finite decoded
Word certificate equals the least repaired-binary64 hull of a nonempty actual
image iff its endpoints are extremal representable bounds. The existing affine
endpoint checker supplies inequalities, not this extra property; a checked
accepted-but-loose example demonstrates the distinction. Closed intervals and
same-parameter partial families inherit the correspondence, preserving empty
fibers. No native rounding, affine-interior optimality or new FP premise follows.

## Finite guarded piece compilation

[Finite guarded pieces](FINITE_GUARD_PIECES.md) supplies a derived restricted
subclass for §§2.13–2.14: rational affine constraints with strict/closed
boundaries, exact union/intersection compilation to finite conjunction pieces,
and an exact rational membership test. It reuses existential piece denotation
and keeps the same parameter/value witness, external restrictions and empty
fibers. This closes a concrete finite-code gap beyond point tables; it is not
a source-prescribed grammar, arbitrary-function representation, automatic
demotion or a full open/exceptional endpoint model. No FP assumption changes.

## Fixed coefficient witnesses and heterogeneous decoding

[Coefficient witnesses](COEFFICIENT_WITNESSES.md) proves exact conversion of
admissible heterogeneous code pairs into real coefficient pairs, retaining one
witness across uses and any joint pair constraint. With 0 and 1 in the parameter
domain, recovery is exactly `(f 0, f 1-f 0)` plus the affine identity. A mixed
integer/rational instance and a strict marginal-versus-joint counterexample are
checked. The existing pointwise coefficient theorem remains unchanged; §2.14's
equality notation alone does not settle persistence of real choices. No new FP
premise or general heterogeneous exceptional endpoint claim is made.

## Mixed affine endpoints and boundary flags

[Mixed endpoints](MIXED_ENDPOINTS.md) proves an exact concrete conversion from
integer/rational lower coefficients and rational/integer upper coefficients to
the existing guarded rational pieces. It preserves open/closed flags, guards,
empty fibers and one band/coefficient witness across uses. A full nonemptiness
criterion distinguishes strict and closed equal endpoints. This closes the
concrete finite mixed-carrier task from the preceding checklist; irrational,
extended/undefined carriers and the full Hansen variant remain separate. The
flags and persistent-choice interpretation are explicit model conventions, not
claims inferred from §2.14. No new FP assumptions or chapter-completion claim.

## Finite Hansen coefficient correspondence

[Finite Hansen coefficients](HANSEN_COEFFICIENTS.md) establishes exact fixed-vector
denotation and attained endpoints for finite closed rational coefficient intervals,
including the printed §2.14 two-point parameter sets. A shared coefficient vector
is retained across repeated uses. Pointwise tightness does not imply a convex
projected image or joint attainment of pointwise extrema. Exceptional/unbounded
carriers and the full system's arithmetic/demotion remain open; Chapter 2 is not complete.

## Possibly unbounded finite-real Hansen coefficients

[Coefficient-set correspondence](HANSEN_REAL_SETS.md) now covers arbitrary sets
of finite real coefficients, strict empty-tuple behavior and zero weights. For
convex coefficient sets it proves exact open-interior membership and a precise
finite-boundary attainment criterion; the existing extended hull is least, but
need not equal the image. Same-parameter demotion and tag-preserving conversion
reuse existing results. Literal infinite/λ coefficient arithmetic and whole-system
operations remain open. These are derived set-model results, not extra printed
Hansen conventions or new IEEE assumptions.

## Uniform §2.5 separation and repaired normalization

[Format normalization](FORMAT_NORMALIZATION.md) proves that `b^M` separates the
printed unsigned digit display from the literal coefficient format for every
`b ≥ 2`, `A ≥ 1`, `m ≤ M`. It also proves equality of the separately labeled
unrestricted repaired and normal-or-minimum value sets at arbitrary radix.
This closes the value-set normalization proof gap, not authorial intent,
exceptional rounding or hardware semantics. The literal definition is unchanged.

## Exceptional right-infinity addition conversion

[Exact family transfer](INFINITE_ADDITION_TRANSFER.md) now connects the existing
source-supported finite/positive-infinity-left addition rows to tagged finite-hull
conversion. It preserves the exact observation image, including missing coverage,
and proves successful-result commutation at the same parameter. No exceptional
arithmetic row is added. Lambda-left and opposite-infinity semantics remain
unresolved here; nonconstant operations require separate transfer proofs.

## Partial square-root conversion

[Root transfer](ROOT_TRANSFER.md) proves sound same-input transfer and exact
observation equality iff input hull conversion admits no new nonnegative finite
values. It separately preserves λ-result existence and unmodeled exceptional
input observations. The checked `(-1,0)` counterexample refutes unconditional
commutation by introducing zero; a disconnected input shows hole filling.
No exceptional arithmetic row or FP premise changes. Automatic criteria and
other partial operations remain separate work.

## Exact partial-operation transfer

[Partial image transfer](PARTIAL_IMAGE_TRANSFER.md) proves a common exactness
criterion for injective partial real graphs and a checked finite-gap certificate,
instantiated by square root and guarded reciprocal. Exact output images preserve
possible definedness, not universal input-domain classification. This advances
the derived §§2.7/2.11 conversion bridge without claiming the full constructive
numeric/domain-description demotion or adding exceptional arithmetic rows.

## Constructive finite value/domain conversion

[Piece-domain conversion](PIECE_DOMAIN_CONVERSION.md) constructs a closed value
enclosure and explicit feasibility code for the existing guarded mixed bands,
preserving each choice's definedness and the family's definite/possible flags.
It does not claim numerical image equality or arbitrary descriptor synthesis.
The [current closeout matrix](CHAPTER2_CLOSEOUT.md) consolidates covered results,
remaining proof gaps, source inconsistencies under stated readings, and
unspecified semantics; it supersedes older residual lists where later proofs
have closed an item. Chapter 2 remains incomplete.

## Guarded composition with generated domains

[Guarded piece composition](GUARDED_PIECE_COMPOSITION.md) connects generated
finite-band descriptors to the existing expression evaluator, with exact domain
classification and sound values on checked success at one parameter and choice.
Failed whole-hull guards remain unknown. The [closeout matrix](CHAPTER2_CLOSEOUT.md)
now distinguishes this covered bridge from missing operation-generated splitting
and output representation for inconclusive guards. No exceptional rows or FP
premises change.

### Affine reciprocal domain splitting

[Generated affine pole pieces](AFFINE_POLE_SPLIT.md) construct exact same-parameter
negative/zero/positive guards for a fixed rational affine denominator (§2.11.4).
The zero piece is explicitly undefined; exact domain testing does not supply a
finite range near a pole. General nonlinear splitting and unbounded value-piece
composition remain open.
