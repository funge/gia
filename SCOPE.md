# General GIA foundations and current applications

The purpose of gia is proving properties of **Generalized Interval Arithmetic**.
Conservative graphing and relgraph's C API are initial applications and comparison
targets, not the definition of the general library. This migration preserves all
proofs and names; it does not silently generalize a restricted theorem.

## Interface findings

| Layer | Actual scope and limitations | Where to read |
| --- | --- | --- |
| Finite arithmetic | QInterval is finite, nonempty, rational-ended, interpreted over reals. Arithmetic enclosure facts have no pixel, raster, C or two-coordinate premise. This is a restricted numerical model, not every generalized interval. | [Intervals](Intervals.lean), [IntervalOps](IntervalOps.lean), [BasicIntervalOps](BasicIntervalOps.lean) |
| Partial values/domains | FunctionalBounds, DomainBounds and PartialEnclosure are parameterized over arbitrary α. UniversalSound also has arbitrary input witnesses W, retaining common witnesses through composition. These general contracts do not assume graphing or totality. | [PartialEnclosures](PartialEnclosures.lean), [UniversalDomains](UniversalDomains.lean) |
| Affine specialization | LinearInterval has one real parameter in [0,1] and rational affine endpoint data. This is a deliberate one-parameter specialization, not a universal dimensional claim or a pixel assumption. | [LinearIntervals](LinearIntervals.lean) |
| Finite covers | FiniteLinearCover covers a relation ℝ → ℝ → Prop on [0,1], without existence. ParameterCell uses closed rational subintervals of [0,1]. These are useful specialized cover foundations, not arbitrary-dimensional coverage. | [FiniteLinearCovers](FiniteLinearCovers.lean), [ParameterRestriction](ParameterRestriction.lean), [CellCoverage](CellCoverage.lean) |
| Continuity | Cell gluing accepts actual real functions and requires continuity and overlap agreement. SemanticContinuity's expression theorem still uses the two-coordinate Expr client. No continuity across jumps/holes is assumed. | [CellContinuity](CellContinuity.lean), [SemanticContinuity](SemanticContinuity.lean), [ConditionalContinuity](ConditionalContinuity.lean) |
| Hardware arithmetic | Bounds are parameterized by a representation type; proofs assume an explicit real decoder and directed-operation/finite-order contracts. No pixels or relgraph data structures are hypotheses. This is conditional correctness, not C/IEEE implementation verification. | [HardwareBounds](HardwareBounds.lean), [hardware guide](HARDWARE_ADDITION.md) |
| Two-variable interpreter | Expr hard-codes x and y, and Value/eval take exactly two coordinates. It is a restricted application/client interface, **not** a general variable environment. Many domain and continuity integrations inherit this restriction. | [Evaluator](Evaluator.lean), [DomainEvaluator](DomainEvaluator.lean), [GuardedEvaluator](GuardedEvaluator.lean) |
| Root/graphing applications | certified_curve_zero is a general scalar IVT result; segment_presence, box search, pixel classification and refinement specialize enclosure/continuity to roots and two-dimensional boxes. They remain valuable applications. | [Presence](Presence.lean), [Subdivision](Subdivision.lean), [AffineRegionSearch](AffineRegionSearch.lean) |

## Concrete coupling retained for a safe migration

`Intervals.lean` mixes QInterval arithmetic with Classification, empty_pixel_sound,
pixelX/pixelY and examples. `empty_pixel_sound` actually proves rectangle zero
exclusion, with no rasterization premise. Its name and location still couple
presentation to graphing. Calling all of this module a pure arithmetic kernel
would be misleading.

There is also import coupling: `UniversalDomains` imports `GuardedEvaluator`,
`ParameterRestriction` imports it too, and `CellContinuity` imports the specialized
`SemanticContinuity`. General signatures need not inherit two-coordinate theorem
assumptions, but consumers still import more application infrastructure than needed.

No theorem/module rename or evaluator rewrite is performed here. The namespace
GeneralizedIntervalArithmetic and Lake package generalized_interval_arithmetic
already express the intended scope. Changing imports now would combine migration
with a proof architecture refactor and complicate auditing #74 separately.

## Follow-up order

1. Extract graphing examples/classification corollaries from Intervals into an
   application module, retaining compatibility imports/names and all audit coverage.
   Keep scalar zero-exclusion as a reusable arithmetic fact.
2. Split parameter/domain/continuity foundation imports from interpreter clients
   where the signatures above permit it; verify the reduced dependency graph.
3. Introduce a genuinely variable-indexed expression interface only as a separate
   design milestone, with proved embeddings of the existing two-variable client.
   Do not relabel Expr as general without changing its actual type.
4. Extend hardware-backed arithmetic and composition with explicit partial domains;
   keep relgraph's operation ledger as one target, alongside a thesis-result roadmap.

For newcomers: start with interval operations, then generic partial/domain
contracts, then affine/cover/continuity specializations. Read the interpreter and
root/graphing applications afterwards. Existing application proofs are preserved,
not deleted or weakened to make the project look more general.
