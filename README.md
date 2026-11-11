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
This review adds cosine and quadrant coverage on [-4,4], retaining the same
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
