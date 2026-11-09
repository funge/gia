> Historical relgraph record: old paths and checks describe their original context.
> For the standalone layout and fresh verification, see [MIGRATION.md](MIGRATION.md).

# Review guide for the Lean milestones

## Current unmerged integration snapshot (2026-11-07)

GitHub metadata was checked for #44–#58 during the domain/search integration
review. All were open and unmerged at the listed heads. This is a dated snapshot,
not merge authorization; recheck before any separately authorized integration.
Main is `8ce2199f6d2d72c0c47269d02b8e1f1aa8cde7f0` (merged through #43).

| PR | Base | Verified head | Role |
| --- | --- | --- | --- |
| #44 | main | `a3c3816` | Independent guarded cancellation |
| #45 | main | `9fb779e` | Independent nonzero-domain certificates |
| #46 | main | `5af426f` | Start of domain-query stack |
| #47 | #46 | `00d1a49` | Quotient domains; copies unchanged #45 core |
| #48 | #47 | `404271d` | Exact rational point completeness |
| #49 | #48 | `a68996d` | Uncertain-input feasibility controls |
| #50 | #49 | `ee23e8e` | Shared-environment prototype |
| #51 | #50 | `c385d0e` | Affine guards |
| #52 | #51 | `9efa154` | Segment domain certificates |
| #53 | #52 | `ba976a5` | Thesis concordance |
| #54 | #53 | `8739adf` | Segment domain completeness |
| #55 | #54 | `e7c60ee` | External-domain presence bridge |
| #56 | #55 | `ad579ed` | Constructive affine regions |
| #57 | #56 | `7b375e9` | Constrained finite search |
| #58 | #57 | `7ea8ab5` | Shared bounded subdivision |

All base SHAs in the #46–#58 chain matched their predecessor heads. #44 and
#45 are independent branches, not ancestors of this chain. The NonzeroDomains
core in #58 is byte-identical to #45, but #45's separate fixture and documentation
are not thereby incorporated. Future integration must reconcile shared audit,
Lake, fixture registration and appended documentation rather than duplicate them.
No merge simulation or combined build with #44/#45 is claimed by this snapshot.
The current validation applies to the #58 tree plus the integration fixture.

`test/domain-search-integration` starts at #58 and adds no production definitions
or mathematical API. Its fresh fixture connects exact singleton analysis to
affine guards for arbitrary generated sums and contrasts domain evidence, missing
ranges, restricted presence and an additional external hole. Read the
[consolidated assessment](INTEGRATION_ASSESSMENT.md#domain-and-search-consolidation-2026-11-07)
before extending the stack. The historical snapshots below remain intact.

## Historical review snapshot: 2026-11-06 23:45 UTC

All 24 GIA PRs below were checked through GitHub: open and unmerged, with each
base branch and base SHA exactly matching the preceding head. #11 targets main
at `158074aaf8df30242efd5b5c40a562bdcacfafd7`. #31 is unrelated and is deliberately
absent. This is a dated snapshot, not a live status indicator or merge approval.

| PR | Base | Verified head | Review focus |
| --- | --- | --- | --- |
| [#11](https://github.com/funge/relgraph/pull/11) | main | `6a00fff` | Segment presence |
| [#12](https://github.com/funge/relgraph/pull/12) | #11 | `f0ede15` | Segment checker |
| [#13](https://github.com/funge/relgraph/pull/13) | #12 | `b750c95` | Finite candidate search |
| [#14](https://github.com/funge/relgraph/pull/14) | #13 | `56cf5b9` | Subdivision coverage |
| [#15](https://github.com/funge/relgraph/pull/15) | #14 | `892e350` | Linear bounds and domains |
| [#16](https://github.com/funge/relgraph/pull/16) | #15 | `97c6dda` | Multiplication |
| [#17](https://github.com/funge/relgraph/pull/17) | #16 | `602ddb8` | Enforced axiom audits |
| [#18](https://github.com/funge/relgraph/pull/18) | #17 | `22817a3` | Polynomial interpreter |
| [#19](https://github.com/funge/relgraph/pull/19) | #18 | `e8b4d03` | Guarded division |
| [#20](https://github.com/funge/relgraph/pull/20) | #19 | `d6355f0` | Local coordinate domains |
| [#21](https://github.com/funge/relgraph/pull/21) | #20 | `df548a0` | Guarded interpreter |
| [#22](https://github.com/funge/relgraph/pull/22) | #21 | `91db4d7` | Piecewise selection |
| [#23](https://github.com/funge/relgraph/pull/23) | #22 | `3adad1a` | Conditional trees |
| [#24](https://github.com/funge/relgraph/pull/24) | #23 | `2f98daf` | Arithmetic composition |
| [#25](https://github.com/funge/relgraph/pull/25) | #24 | `8f6a7b4` | First consolidation |
| [#26](https://github.com/funge/relgraph/pull/26) | #25 | `796cc60` | Parameter restriction |
| [#27](https://github.com/funge/relgraph/pull/27) | #26 | `58693da` | Defined arithmetic continuity |
| [#28](https://github.com/funge/relgraph/pull/28) | #27 | `6cfa21c` | Closed-cell gluing |
| [#29](https://github.com/funge/relgraph/pull/29) | #28 | `013c2c6` | Threshold continuity |
| [#30](https://github.com/funge/relgraph/pull/30) | #29 | `f409ade` | Finite covers |
| [#32](https://github.com/funge/relgraph/pull/32) | #30 | `37e6dd5` | Conditional cover domains |
| [#33](https://github.com/funge/relgraph/pull/33) | #32 | `c7264ff` | Domain-certified presence |
| [#34](https://github.com/funge/relgraph/pull/34) | #33 | `7ba5b92` | Coalescing and size limits |
| [#35](https://github.com/funge/relgraph/pull/35) | #34 | `a72069e` | Finite-cover restriction |

Review in dependency order, using each PR's predecessor base for its mathematical
delta. The current consolidation branch `test/finite-cover-integration` starts
at #35 and adds independent tests and review guidance, not a new core interface.
The refreshed assessment is at the end of
[INTEGRATION_ASSESSMENT.md](INTEGRATION_ASSESSMENT.md).

Before any separately authorized merge sequence, recheck heads and ancestry.
Squashing or rewriting an early branch can make downstream PRs repeat already
reviewed changes; do not mechanically retarget or force-push the stack. No merge,
rebase, retarget or history rewrite was performed for this snapshot.

## Historical milestone guidance

This is a review snapshot as of 2026-11-06. PRs #11–#15 were verified open and
unmerged when the multiplication milestone was prepared. All work is isolated
under `formalization/lean`; no native release dependency or hosted CI is added.
No merge is authorized by this guide.

Each PR targets its immediate predecessor, so its Files changed view shows only
that milestone. Review in the following order. Commit IDs identify the original
milestone heads; this table is historical evidence, not a promise that branches
will never move.

| PR / branch | Base | Scope | Original head |
| --- | --- | --- | --- |
| [#11](https://github.com/funge/relgraph/pull/11) | main | Continuous-segment presence and expression continuity | `6a00fff` |
| [#12](https://github.com/funge/relgraph/pull/12) | #11 branch | Executable supplied-segment certificate and three outcomes | `f0ede15` |
| [#13](https://github.com/funge/relgraph/pull/13) | #12 branch | Finite candidate search and optional eight-segment policy | `b750c95` |
| [#14](https://github.com/funge/relgraph/pull/14) | #13 branch | Bounded subdivision, coverage, conservative aggregation | `56cf5b9` |
| [#15](https://github.com/funge/relgraph/pull/15) | #14 branch | Linear parameter bounds and partial-domain contracts | `892e350` |
| `feat/linear-multiplication` | #15 branch | Product enclosure and domain preservation | See this PR head |

The stack order preserves the published review history. It does not mean all
mathematical modules depend on graph search: `LinearIntervals` imports ordinary
interval foundations, `PartialEnclosures` imports `LinearIntervals`, and
`LinearMultiplication` imports `PartialEnclosures`. There is no import from the
new arithmetic modules into the old expression evaluator or presence/search
modules. Future integration is separate work.

## Focus for the multiplication review

1. Check the exact product identity and the `t(1-t)` error bound. The one-sided
   correction must have the right sign for both positive and negative curvature.
2. Check join containment on `[0,1]` and the four-corner product argument. The
   theorem quantifies over independent operand values at one shared parameter.
3. Check all three clauses of `linear_mul_domain_sound`: value enclosure,
   possible domain membership, and existence from definite membership.
4. Check examples and stated limitations, especially that zero times an undefined
   operand stays undefined and that square bounds are not claimed optimal.

The new proof module and examples are the mathematical delta. `Audit.lean`, the
Lake target list, README links, this guide, the milestone notes, and the appended
validation record make that delta buildable and reviewable. Prior proof files and
validation records remain intact.

## Local validation

From `formalization/lean`, with the pinned Lean toolchain available:

```
lake build
lake env lean Audit.lean
```

The default build includes all earlier examples through existing targets/imports
and the new multiplication examples. Audit output is cumulative; each milestone's
historical count and commands remain recorded in `VALIDATION.md`. No `sorry`,
new axiom, or native evaluation proof shortcut is used. Standard Lean/mathlib
axioms are listed explicitly in the records.

After any separately authorized merges, compare actual branch ancestry before
retargeting remaining PRs. This guide does not perform merges, rebases, or force
pushes, and no history rewrite was needed to prepare this milestone.

The subsequent enforced-audit milestone makes `Audit` a default build target.
See [AUDIT_POLICY.md](AUDIT_POLICY.md) for the allowlist, imported-namespace
coverage, failure-path controls, and trust limits. Earlier counts remain
historical named-audit counts.

## Subsequent review increments

- [#16](https://github.com/funge/relgraph/pull/16): multiplication, based on #15;
  original head `97c6dda`.
- [#17](https://github.com/funge/relgraph/pull/17): enforced axiom audit, based on
  #16; original head `602ddb8`. This changes validation, not mathematical claims.
- `feat/linear-expression-evaluator`: polynomial interpreter bridge, based on
  #17. Review `evalLinear_sound` and `evalLinear_defined` separately, then the
  partial-domain bridges and the unsupported-but-defined division control.

The interpreter imports the existing syntax/semantics and linear arithmetic,
not continuity or graph search. Division and external coordinate-domain analysis
remain outside its scope. The existing evaluator is not replaced.

- [#18](https://github.com/funge/relgraph/pull/18): polynomial interpreter,
  based on #17; original head `22817a3`.
- `feat/guarded-linear-division`: standalone reciprocal/quotient operations,
  based on #18. Review the hull guard, partial quotient relation, and all three
  domain-contract clauses. It does not alter the interpreter under review.

- [#19](https://github.com/funge/relgraph/pull/19): guarded arithmetic operations,
  based on #18; original head `e8b4d03`.
- `feat/domain-local-evaluator`: domain-local interpretation contracts, based on
  #19. Its proofs depend on #18's interpreter and existing domain contracts,
  not on the guarded division implementation. Review the strict two-coordinate
  environment definition and the three domain-contract obligations; the
  non-global-enclosure example demonstrates the relaxed premise explicitly.

- [#20](https://github.com/funge/relgraph/pull/20): domain-local contracts,
  based on #19; original head `d6355f0`.
- `feat/guarded-expression-evaluator`: arithmetic/domain integration, based on
  #20. Review local definedness premises and the denominator nonzero proof,
  then exact polynomial compatibility and the domain bridges. The counterexample
  to global definedness and manually constructed semantic value are key controls.
  Existing #17–#20 proof files and policy are not rewritten by this integration.

- [#21](https://github.com/funge/relgraph/pull/21): guarded interpreter integration,
  based on #20; original head `df548a0`.
- `feat/piecewise-domain-selection`: external branch selection, based on #21.
  Review the global decision contract, strict comparison boundaries, and
  definite-intersection/possible-union rule. Inspect the independently proved
  discontinuous jump and the inactive/active undefined-branch controls. This
  does not extend Expr or promise lazy execution of failing branch code.

- [#22](https://github.com/funge/relgraph/pull/22): external piecewise selection,
  based on #21; original head `91db4d7`.
- `feat/conditional-expression-trees`: finite conditional wrapper, based on #22.
  Review guard Value requirements, equality selecting false, the unknown case's
  two-branch requirement, and local definedness. Inspect actual pole/undefined-
  guard controls and exact inactive-branch independence. Neither the original
  Expr nor #22's total-predicate contract is rewritten.

- [#23](https://github.com/funge/relgraph/pull/23): partial conditional trees,
  based on #22; original head `3adad1a`.
- `feat/conditional-arithmetic-composition`: arithmetic distribution through
  trees, based on #23. Review exact semantic equivalence before the enclosure
  corollaries, discharge of generic transformation premises for all four ops,
  and nonzero/strict-operand requirements. Check both the branchwise reciprocal
  improvement and the everywhere-defined correlated example returning unknown.
  No existing evaluator, expression grammar, or continuity claim changes.

- [#24](https://github.com/funge/relgraph/pull/24): conditional arithmetic,
  original head `2f98daf`.
- [#25](https://github.com/funge/relgraph/pull/25): integrated assessment and local
  validation controls, original head `8f6a7b4`; no library API changes.
- `feat/parameter-restriction`: based on #25. Review affine composition and the
  degenerate surjectivity case, domain precomposition versus numerical success,
  and transfer through a supplied cover. The examples reuse split_cover and
  split_boundary; there is no second subdivision algorithm or continuity claim.

- [#26](https://github.com/funge/relgraph/pull/26): parameter restriction and
  supplied coverage, original head `796cc60`.
- `feat/defined-arithmetic-continuity`: based on #26. Review the extraction of
  nonzero denominators from Value, the distinction between relative and whole-
  interval continuity, and the explicit coordinate continuity/enclosure
  premises. Check the positive IVT integration and punctured-domain no-root
  counterexample. This does not glue cells or add a conditional continuity rule.

- [#27](https://github.com/funge/relgraph/pull/27): arithmetic semantic continuity,
  original head `58693da`.
- `feat/closed-cell-continuity`: based on #27. Review positive-width inverse
  versus singleton handling, finiteness and closedness in the union theorem,
  and common-function agreement over all overlaps. Inspect the independent
  transfer of actual values before IVT and the jump/gap/domain-hole controls.

- [#28](https://github.com/funge/relgraph/pull/28): finite closed-cover continuity,
  original head `6cfa21c`.
- `feat/threshold-conditional-continuity`: based on #28. Review actual guard
  equality to the parameter, the distinction between a true-branch continuous
  extension and its actual boundary value, and false-branch equality selection.
  Check jump/active-hole/guard-hole controls and the positive #28 wrapper
  regression with distinct representatives agreeing over a full overlap.

- [#29](https://github.com/funge/relgraph/pull/29): threshold conditional continuity,
  original head `013c2c6`.
- `feat/finite-linear-covers`: based on #29. Review the enclosure-only contract,
  certified selection, all-component reciprocal traversal, and its explicit
  nonzero relational semantics. Check actual-value witnesses separately from
  range exclusion. No scalar interpreter return type or domain API is changed.

- [#30](https://github.com/funge/relgraph/pull/30): finite linear covers,
  original head `f409ade`.
- `feat/conditional-cover-domains`: based on #30. Review exact success
  correspondence with the scalar evaluator, lazy known choices versus required
  unresolved branches, and local coordinate hypotheses. Check all three domain
  obligations through reciprocal evaluation and the environment-hole controls.

- [#32](https://github.com/funge/relgraph/pull/32): conditional cover/domain
  integration, original head `37e6dd5`.
- `feat/domain-certified-cover-presence`: based on #32. Review whole-path
  definite membership versus continuous extension, actual-value agreement,
  endpoint sign quantification over all components, and extraction of an actual
  zero after IVT. Check the same-cover punctured-domain no-root control.

- [#33](https://github.com/funge/relgraph/pull/33): domain-certified cover presence,
  original head `c7264ff`.
- `feat/finite-cover-coalescing`: based on #33. Review inclusion direction,
  unchanged domain predicates, singleton equivalence, zero-capacity handling,
  and the output-length proof. The policy is postprocessing, not a runtime
  resource bound. Check strict precision loss and retained root/domain controls.

- [#34](https://github.com/funge/relgraph/pull/34): sound finite-cover coalescing,
  original head `7ba5b92`.
- `feat/finite-cover-restriction`: based on #34. Review exact membership under
  the existing cell map, unit-range guards, both pulled-back domain directions,
  and the fresh conditional interpreter bridge. Check multivalued semantics,
  noncommuting coalescing order, degenerate holes, and retained boundary absence.

- [#36](https://github.com/funge/relgraph/pull/36): independent cover pipeline and
  review consolidation, original head `b63f1da`.
- `feat/fuelled-cell-certificates`: based on #36. Review the instrumented call
  counter versus actual runtime costs, early failure/exhaustion behavior, and
  the separate ParameterCover premise. The consumer derives arithmetic
  continuity only for continuous enclosed coordinates, without inferring
  membership in external partial environments. Check gap/pole/empty-list controls.

- [#37](https://github.com/funge/relgraph/pull/37): fuelled cell certificates,
  original head `df385da`.
- `feat/checked-cell-coverage`: based on #37. Review the ordered coverage scan,
  nondecreasing covered endpoint, closed boundaries and soundness conversion to
  ParameterCover. The combined consumer removes only the manual coverage premise;
  coordinate conditions remain. Check rejected valid reversed covers, gaps,
  overlaps and redundant-tail exhaustion. Geometry work is outside the call budget.

- [#38](https://github.com/funge/relgraph/pull/38): checked cell coverage,
  original head `0a8582f`.
- `feat/adaptive-cell-certificates`: based on #38. Review retained unresolved
  leaves, shared boundaries, two-way geometric containment, and planning plus
  revalidation call accounting. No completeness or absence claim follows from
  exhaustion. The fresh root client supplies no cells; the pole control rejects
  certification for every pair of budgets.

- [#39](https://github.com/funge/relgraph/pull/39): adaptive cell certificates,
  original head `ddd65eb`.
- `feat/finite-cover-products`: based on #39. Review Cartesian member/length
  proofs and the existing ProductValues/DomainBounds.inter contract. Test the
  distinction between shared parameter and correlated witnesses: mixed products
  must survive, while correlated square values cannot be inferred from enclosure.
  The core-only pipeline retains a real domain hole through multiplication.

- [#40](https://github.com/funge/relgraph/pull/40): finite-cover multiplication,
  original head `3b21095`.
- `feat/shared-witness-squares`: based on #40, extending the same arithmetic
  module. Review the one-witness SquareValues contract and its single-valuedness
  bridge, not a substitution for independent ProductValues. The fresh pipeline
  preserves a hole and tests the precision lost by coalescing before squaring.

- [#41](https://github.com/funge/relgraph/pull/41): shared-witness squares,
  original head `316364c`.
- `feat/threshold-local-certificates`: based on #41. Review actual guard identity
  as an explicit premise, local parameter provenance, equality on the false
  branch, and conservative closed-cell checks. New independent fixture contrasts
  jump exclusion, active/inactive boundary poles, and an undefined guard. No
  continuity conclusion or replacement of global interpreter semantics is made.

- [#42](https://github.com/funge/relgraph/pull/42): threshold-local certificates,
  original head `ed5a624`.
- `proof/finite-cover-boundedness`: based on #42. Three general theorems establish
  uniform boundedness and impossibility for unbounded actual relations. The
  existing threshold fixture contrasts an everywhere-defined unbounded branch
  (no finite global/local cover) with bounded guarded cancellation (a cover
  exists but the checker returns unknown). No evaluator behavior is changed.

## Independent executable domain-query prerequisite (2026-11-07)

`feat/executable-domain-queries` starts directly at merged main
`8ce2199f6d2d72c0c47269d02b8e1f1aa8cde7f0`. It is independent of pending #44 and
#45. Review the single query definition and five proofs in `DomainQueries.lean`,
then the fresh rational partial-expression fixture. Supplied domain decisions
are required; unknown certifies neither presence nor absence. The semantic
wrappers deliberately consume domain-only evidence. Separate scratch validation
checked compatibility with #45 without introducing a source/build dependency.
See the appended validation record. No new merge authorization is implied.

## Automatic outer-quotient domain integration (2026-11-07)

`feat/automatic-quotient-domains` is based on #46 and additionally includes the
unchanged `NonzeroDomains.lean` core from #45. Review against #46: the 55-line
prerequisite is byte-identical to #45, and the new mathematical work is in
`QuotientDomains.lean` plus its fresh client. This explicit prerequisite avoids
merging or altering either pending PR; its three theorem audits and Lake entry
are included so this branch builds independently. Reconcile shared registration
and appended documentation when integrating the reviewed branches later.

The automatic scope is one outer quotient with successfully guarded children.
Both operands use fixed shared coordinates and a common external domain.
Failed analysis preserves unknown; absence can still follow from an external
exclusion. Numerical refinement and semantic certificates are linked by proofs,
not assumed equivalent. No new merge authorization is implied.

## Exact-point precision increment (2026-11-07)

`feat/exact-point-domains` is based on #47. Review `PointDomains.lean`: the
foundation is a success/existence theorem for a sound backend and a completeness
theorem restricted to exact-backend rational singleton inputs. The domain wrapper
reuses the original evaluator's recursion. Then review the fresh PointDomains
fixture, especially the independent nested reciprocal equivalence and the
counterexamples showing why general interval/backend failure remains unknown.

No existing evaluator or classifier result is changed. External domains remain
explicit. This does not resolve recursive uncertain-interval range/domain
analysis; it is a separately justified exact-input path. See appended validation.
No new merge authorization is implied.

## Uncertain-input feasibility and regression controls (2026-11-07)

`test/uncertain-domain-feasibility` is based on #48. Review the appended
INTEGRATION_ASSESSMENT discussion and the fresh UncertainDomains fixture.
There are no production Lean module changes. The fixture distinguishes
independent projected child existence from a common expression environment,
checks a safe uniform alternative, preserves external holes, and applies the
finite-range limitation to an uncertain reciprocal input.

This is an assessment milestone, not a new recursive analyzer. The proposed next
design retains a shared environment until constraints are combined and treats
unavailable range information separately. No representation choice is silently
implemented and no new merge authorization is implied.

## Representation comparison with test-only prototype (2026-11-07)

`test/shared-environment-prototype` is based on #49. Review the representation
comparison appended to INTEGRATION_ASSESSMENT, then OptionalRangePrototype.
The experimental structure is confined to a fresh fixture and does not change
production interfaces. The critical obligations are faithful embedding, shared
environment composition, and separation of missing range information from domain
membership. All are kernel-checked; full validation is recorded separately.

The comparison recommends domain precision first, with partitions as a later
refinement and richer ranges deferred. No general constraint syntax, projection
solver, multidimensional cell representation or unbounded arithmetic is adopted.
No new merge authorization is implied.

## Finite affine guard increment (2026-11-07)

`feat/affine-domain-guards` is based on #50. Review AffineDomainGuards and its
fresh fixture: the main obligation is exact partial-domain equivalence of the
existing generated Expr with a finite conjunction at one common real environment.
The executable rational check is linked by a cast theorem and retains the
external DomainBounds. Earlier APIs and the test-only optional-range prototype
are not migrated.

The family is sums of reciprocal rational-affine forms, not an arbitrary AST
recognizer or a solver for projected region feasibility. Both real semantic
counterexamples and executable queries are checked. See the appended validation
and scope records. No broad representation choice or new merge authorization is
implied.

## Affine segment-domain integration (2026-11-07)

`feat/affine-segment-domains` is stacked directly on #51
(`c385d0e08284c82429eca53beedde64edd2efdaf`). Review the new module and fresh
fixture, then five named audit registrations and module/fixture registration.
Existing production APIs are unchanged. Main mathematical obligations are
affine interpolation, strict nonzero guards across the entire segment, and
reuse of derived continuity with endpoint enclosures. See scope and validation
records for external-domain and orientation limits. No merge authorized here.

## Thesis concordance documentation (2026-11-07)

`docs/thesis-concordance` is based on #52 at
`9efa154bd09e8a9a2198974da6aaf1e37102746c`. The focused documentation change adds
[THESIS_CONCORDANCE.md](THESIS_CONCORDANCE.md), links it from the README, and
clarifies the exact-rational-singleton exception to general evaluator failure.
The concordance distinguishes merged and reviewed source, exact examples,
restricted/conditional counterparts, missing topics, and project extensions.
No mathematical sources or dependency/build configuration change.

## Restricted segment-domain completeness (2026-11-07)

`feat/affine-segment-domain-completeness` is based on #53 at
`ba976a57f4060352efa1c1d0f283e2e8438e186e`. This increment strengthens the existing
segment-domain specification with two converse/equivalence theorems and extends
its existing independent fixture. No executable definition or classifier changes.
Review especially the distinction between a hole somewhere, no values anywhere,
and absence of zeros. The private intermediate-value helper is audited through
its public theorem dependencies. No new thesis-proof correspondence is asserted.

## External-domain presence bridge (2026-11-07)

`feat/affine-presence-domain-bridge` is based on #54 at
`8739adff1b4fd8169c03cc1634017d3fee88555c`. The existing presence proof is factored
to retain its path witness; the old public statement and executable definitions
are preserved. Four added public theorems connect restricted definedness,
path-level presence, external-domain presence and restricted absence. Review the
whole-path premise and the endpoint-only counterexample. No additional domain
solver, FP assumptions, source-access attempts or exact-thesis claims are added.

## Affine external-region checks (2026-11-07)

`feat/affine-external-domain-checks` is based on #55 at
`e7c60ee7fd295ebe4630ff44bee400b0edced30a`. Review AffineRegions and its independent
fixture, then module/fixture and five public-theorem audit registrations.
The finite constraint language denotes closed half-space conjunctions exactly;
the three-way decision has whole-path semantics. Positive inclusion feeds the
existing presence theorem. Negative path exclusion must not be read as box
absence, and unknown must not be read as infeasibility. Prior APIs are unchanged.

## Affine-region finite search (2026-11-07)

`feat/affine-region-segment-search` is based on #56 at
`ad579edf1a378a6dde1264770cca6f1373ba99cc`. Review AffineRegionSearch and its
fresh fixture, then module/fixture registration and seven public-theorem audits.
It reuses the established candidate type, eight-segment policy, List.find?, and
ResultSound. The main obligations are restricted root soundness for both sign
orientations and keeping search exhaustion/path exclusion separate from box
absence. No existing algorithm, FP contract or exact-thesis claim changes.

## Affine-region bounded subdivision (2026-11-07)

`feat/affine-region-subdivision` is based on #57 at
`7b375e95ab5ff311f2c87759d78e9ac79b33194e`. Review the small shared-engine
extraction in Subdivision first: the old public API and defining equations remain.
Then review AffineRegionSubdivision's fixed-region split equivalences and sound
instantiation, followed by the fresh independent fixture. Seven public theorems
are added to named audits. No duplicated recursion or evaluator is introduced.
Check especially that unknown never becomes empty merely because paths fail,
that both closed children cover the parent, and that domain restrictions remain
unchanged. No FP contract, source-access workaround or exact-thesis claim changes.

## Integration preparation after #59 (2026-11-07)

The [merge plan](MERGE_PLAN.md) refreshes exact heads through #59 and records
actual tree-only conflict analysis for the independent #44/#45 branches. Targeted
checks passed for their original fixtures against #59 libraries. No resolved
combined tree was built, and no merge, retarget or rebase was performed. Follow
the plan only after separate authorization and fresh qualification of heads.

## Finite-rational affine correspondence (2026-11-07)

`proof/affine-coefficient-correspondence` starts at the source-review PR #61,
`be6fc0b2f4b438aa391597f5585bc77b1a0b6e6d`. Review the additions to existing
LinearIntervals, then seven named audits and the fresh AffineCorrespondence
fixture. No new root module or replacement evaluator is introduced. Source
hypotheses and finite-rational restrictions are stated in the concordance and
generalized-interval guide. The local combined #44/#45 rehearsal remains separate;
this branch does not integrate those independent heads.

## Constant-interval embedding (2026-11-07)

`proof/constant-interval-embedding` starts at #62,
`3b317c38df9cbeb482df7e18db3670bd23f01898`. Review the existing-module theorem
additions, seven named audits and fresh ConstantEmbedding fixture. There is no
new root module, evaluator, domain representation or FP premise. Check the
source's interval-extension qualification against the deliberately restricted
operation equalities, and preserve the one-way success premise in the interpreter
bridge. The independent #44/#45 rehearsal remains outside this branch.

## Quadratic chord correction bridge (under review)

`proof/quadratic-chord-corrections` builds on #63 at
`4845d6bd2f2d53ea1fa44ed65b9500c456c54d70`. Four theorems in the existing
LinearMultiplication module connect finite quadratic coefficients to necessary
and sufficient fixed-chord corrections. No new evaluator, root module, FP
contract or domain convention. This is a restricted bridge following thesis
§2.9.5, not its complete extended-real representation or demotion algorithm.
The separate #44/#45 rehearsal does not include this branch.

## Two-parameter affine validity (under review)

`proof/two-parameter-affine-order` builds on #64 at
`d8b7352aa8bc7e203e1142a4719c3f259ed346de`. Four proved contracts and one
Boolean test reuse RationalAffineForm and FunctionalBounds to characterize
whole-unit-square non-collapse by four corners. A false result is not absence;
no existing domain or evaluator behavior changes. Thesis §§2.9.6–2.9.7 are
specialized to two independent parameters and finite rational coefficients.
The separate combined-tree rehearsal does not include this milestone.

## Universal input-domain milestone (under review)

`proof/universal-input-domains` builds on #65 at
`e2c806c09b043cda292c1b176cfe0db35bacf902`. One module groups the source-domain
compatibility interpretation, input-indexed contract, old-contract projection,
exact logical domain envelope and precision, same-input addition, restriction,
and guarded evaluator integration. Existing APIs and domain behavior remain
unchanged. The source match is restricted and documented; no FP change or merge.
The separate combined-tree rehearsal excludes this later milestone.

## Square-root domain model (under review)

`proof/square-root-domain-model` builds on #66 at
`35eec824008be8f9bd9510431f74f4c94b1a0bf2`. The exact-real counterpart of the
paper's three-branch square-root algorithm is proved sound under UniversalSound,
with partial semantics, branch characterizations and composition controls.
Original thesis/paper differences and the loose but sound thesis example are
recorded. No Expr syntax, FP assumptions, merge or implementation claim.
The separate combined-tree rehearsal excludes this milestone.

## Property-composition source review (under review)

`test/property-composition-source-review` builds on corrected #67 at
`59d376a668e142b69051ab6cd46bfbff9b30df94`. It adds a registered independent
fixture proving the sufficient continuity-composition direction and refuting
the literal unary specialization of the printed weak direction. Documentation
records the source pages and defers a generic property API pending a precise
specification decision. No production Lean API, FP assumption or merge change.


<!-- Historical material from PR #44; original milestone claims and validation follow unchanged. -->

- [#43](https://github.com/funge/relgraph/pull/43): finite-cover boundedness,
  original head `a3500ad`.
- `feat/guarded-threshold-cancellation`: based on #43. Review the actual nonzero
  premise supplied by the true guard, bidirectional value equivalence, retained
  guard/false branch, and transport of all SoundOn clauses. The existing fresh
  fixture contrasts certified removable cancellation with unguarded zero
  division, undefined guards, false-branch poles and true unbounded ranges.


<!-- Historical material from PR #45; original milestone claims and validation follow unchanged. -->

## Post-merge independent domain certificate increment (2026-11-07)

The earlier stack through #43 has been merged under explicit authorization.
`feat/nonzero-domain-certificates` starts at merged main
`8ce2199f6d2d72c0c47269d02b8e1f1aa8cde7f0`; it does not depend on #44, which
remains open for review. Review `NonzeroDomains.lean` (two definitions and three
soundness theorems), then its fresh core-only client. Domain certification is
separate from range evaluation. The existing quotient relation retains
independent operand witnesses. See the appended validation record and domain
scope notes. No new merge is authorized by this record.
