> Historical relgraph record: old paths and checks describe their original context.
> For the standalone layout and fresh verification, see [MIGRATION.md](MIGRATION.md).

# cloud validation

The dated records below retain the paths, module names, namespaces, and log output
used at the time. The current project is `generalized-interval-arithmetic` in
`formalization/lean`, with package `generalized_interval_arithmetic` and namespace
`GeneralizedIntervalArithmetic`. Each rename has fresh validation appended below.

Validated on 2026-11-06 in the saved relgraph cloud environment.

## checkout and isolation

- Starting branch: `work`; starting commit:
  `c467d390a66b48618f3e1d627980e5c0a2bfcc32`.
- Starting working tree: clean.
- Pilot branch: `pilot/lean-interval-enclosure`.
- All repository changes are under `formalization/lean-pilot/`.
- No `AGENTS.md` or repository `.agents/skills` was present. The available
  `CONTRIBUTING.md`, README, and numeric contract were inspected.
- No C source, native build, native tests, release configuration, or hosted CI
  was modified. Native suites were not rerun because the change is isolated to
  the optional Lean project. Nothing was pushed, merged, or opened as a PR.

## actual results

Commands ran from `formalization/lean-pilot` with
`/workspace/lean-tools/lean-4.19.0-linux/bin` prepended to `PATH`.

| command | result |
| --- | --- |
| `lean --version` | `Lean (version 4.19.0, x86_64-unknown-linux-gnu, commit 6caaee842e94, Release)` |
| `MATHLIB_NO_CACHE_ON_UPDATE=1 lake update` | exit 0; pinned mathlib and eight transitive packages downloaded; lockfile generated |
| `lake build` | exit 0; source dependency build and `RelgraphPilot` succeeded; no warnings or errors |
| `lake env lean Audit.lean` | exit 0; all nine theorem audits list only `propext`, `Classical.choice`, `Quot.sound` |
| `lake build` (warm repeat) | exit 0; `Build completed successfully.` |
| source scan for `sorry`, `admit`, and `axiom` declarations | no matches in the two pilot Lean files |

The first build ended with:

```text
✔ [730/733] Built Mathlib.Tactic.NormNum
✔ [731/733] Built Mathlib.Data.Real.Basic
✔ [732/733] Built RelgraphPilot
Build completed successfully.
```

The audit covers `add_encloses`, `sub_encloses`, `classify_empty_sound`,
`empty_pixel_sound`, `example_bounds`, `example_classification`,
`example_empty_pixel`, `zero_boundary_unknown`, and
`unknown_does_not_imply_root`, all in namespace `RelgraphPilot`. None depends on
`sorryAx` or any newly declared axiom. The three listed axioms are the standard
Lean/mathlib foundations, not project-specific assumptions.

Full local execution logs are at `/workspace/lean-tools/pilot-build.log` and
`/workspace/lean-tools/pilot-audit.log`; these are environment-local evidence,
not required source files.

## network and persistence limitations

The runtime reported current observations, an enforced restricted HTTP policy,
the package-manager preset, and no configured credentials or VPN. The official
Lean release and GitHub dependency downloads succeeded through the inherited
proxy and CA configuration.

The pinned mathlib cache client targets
`https://lakecache.blob.core.windows.net/mathlib4`, whose host is absent from the
effective allowlist. Cache fetching was therefore **not attempted**. Dependencies
were compiled from source instead. This was a configuration limitation, not an
observed denied request, and it did not prevent validation. No access restriction
was bypassed, no approval was requested, and no network policy was changed.

There is no remaining build blocker in this instance. A warm rebuild worked;
reuse or persistence across a newly launched cloud task has not been tested.
The toolchain and `.lake` contents are not committed, so a fresh environment must
install the pinned toolchain and fetch/build the locked dependencies again.

This validates the abstract proof only. It does not establish floating-point
enclosure or implementation correctness; see the scope and limits in `README.md`.

## conditional rounding follow-up (2026-11-06)

Continued from local commit `7d1218644551bb32952c8211f96bfddb96eb1156` on the same
pilot branch, with a clean starting tree. The existing toolchain and dependency
build were available in this resumed environment. No package or toolchain changes
were needed, and the original `RelgraphPilot.lean` proofs remain unchanged.

John explicitly allowed assuming rounding modes and asked to check before
complicating FP assumptions. Accordingly, `RoundedPilot.lean` proves the
consequence of two local outward-rounding inequalities. IEEE 754 is the reference
for the intended directions. This is not an unconditional FP implementation
proof. The README states the assumptions, format interpretation, and edge cases.

- `lake build`: exit 0, `Built RoundedPilot`, `Build completed successfully.`
- `lake env lean Audit.lean`: exit 0. All 13 audited declarations (12 theorems
  and the new interval constructor) depend only on
  `[propext, Classical.choice, Quot.sound]`; no `sorryAx` or new axioms.
- No new dependencies, network-policy changes, application-build changes, or
  hosted workflows. No build blocker or denied action occurred.

The new theorem names are `rounded_add_encloses`, `rounded_add_empty_pixel`, and
`halfway_candidate_bounds`, in namespace `RelgraphPilot`. `roundedAdd` is the
constructor. The pilot's default `lake build` now includes both proof modules;
the root application/native build remains independent.

## compositional evaluator milestone (2026-11-06)

Started from `121a221e0016ec321160223745d37ed94c6b0f70` on
`pilot/lean-interval-enclosure`, with a clean tree. The existing toolchain and
dependency objects were reused. The earlier proof sources, dependency lockfile,
and Lean pin are unchanged; no new packages or FP models were installed.

Implemented the exact evaluator, partial real semantics, guarded division,
structural enclosure theorem, zero-exclusion theorem, and a conditional
directed-rounding adapter. `EVALUATOR.md` states the exact scope and assumptions.

Final commands, run in the pilot directory with the same pinned `PATH`:

| command/check | observed result |
| --- | --- |
| `lake build` | exit 0; `EvaluatorPilot`, `EvaluatorRounding`, and `EvaluatorExamples` built; `Build completed successfully.` |
| `lake env lean Audit.lean` | exit 0; 44 audited declarations, all using only `[propext, Classical.choice, Quot.sound]` |
| audit coverage check | every public theorem in the four new Lean modules appears in `Audit.lean` |
| source scan | no `sorry`, `admit`, new `axiom`, or `native_decide` in the pilot Lean sources |
| `git diff --check` | exit 0 |
| diff against prior commit for native files, earlier proof sources, and dependency pins | no changes |

Full audit output: `/workspace/lean-tools/evaluator-audit.log` (environment-local).
The audit includes the concrete examples and the synthetic widening backend's
proved contracts. Generic backend/rounding assumptions remain explicit theorem
parameters; the axiom audit does not mean those hypotheses have been verified for
hardware or C code. The exact backend's contract is proved, not assumed.

During development, ordinary `decide` could not unfold some rational order
instances, and broad `norm_num` simplification hit heartbeat limits on guarded
examples. Final finite computations use `decide +kernel`, which reduces and
checks the decision procedure in Lean's kernel. No native-evaluation axiom or
increased heartbeat limit was introduced. These proof-script issues are resolved;
the final build reported no warnings or errors.

The denominator guard is proved to exclude zero on success and to return unknown
for zero-containing intervals, including zero endpoints. Real semantic division
requires a nonzero denominator; `1/0` is proved to have no semantic value.
The dependency-loss example is separately proved defined at every real point,
so unknown is demonstrably not an undefinedness verdict.

No remaining build blocker or denied action. Application/release files and hosted
CI remain untouched. No push, PR, or merge was performed. The only FP contracts
are the previously authorized outward endpoint inequalities, now conditional on
successful optional finite conversion. No exceptional-value semantics or
implementation-correctness claims were added.

## durable naming and fresh validation (2026-11-06)

Starting commit: `16fc1d2b2f2ff88ddbeae8ef9e224c09171c2b9b`. The earlier records
above preserve the original names and logs; their no-push/no-PR statements refer
to those earlier validation runs. PR #10 was subsequently opened in
`funge/relgraph`. This rename updates that PR on its existing branch
`pilot/lean-interval-enclosure`; neither the repository nor the PR branch is
renamed.

| prior name | current name |
| --- | --- |
| `formalization/lean-pilot` | `formalization/lean` |
| package `relgraph_lean_pilot` | `interval_graphing` |
| namespace `RelgraphPilot` | `IntervalGraphing` |
| module `RelgraphPilot` | `Intervals` |
| module `RoundedPilot` | `RoundedAddition` |
| module `EvaluatorPilot` | `Evaluator` |

`IntervalOps`, `EvaluatorRounding`, `EvaluatorExamples`, and `Audit` retain their
descriptive module names. Imports, audit targets, Lake targets, and current
documentation use the new names. Actual repository references remain accurate.

Fresh commands ran from `/workspace/relgraph/formalization/lean`, using the same
pinned toolchain and dependencies:

- `lake build`: exit 0; rebuilt `Intervals`, `RoundedAddition`, `IntervalOps`,
  `Evaluator`, `EvaluatorRounding`, and `EvaluatorExamples` without warnings or
  errors; `Build completed successfully.`
- `lake env lean Audit.lean`: exit 0; all 44 declarations now appear under
  `IntervalGraphing`, with only `[propext, Classical.choice, Quot.sound]`.
- Source comparison with the starting commit: all seven Lean files are identical
  after the intended module/namespace substitutions and introductory comment
  rename. No proof statements, assumptions, or proof bodies otherwise changed.
- Dependency manifest comparison: only the root package name changed; dependency
  revisions and the toolchain pin are unchanged.
- `git diff --check`: passed. Changes remain confined to the Lean project.

Fresh logs are `/workspace/lean-tools/interval-graphing-build.log` and
`/workspace/lean-tools/interval-graphing-audit.log`. Earlier log paths are retained
above as historical evidence, not rewritten to suggest they used today's names.
No remaining build blocker or denied action occurred.

## broader project name and fresh validation (2026-11-06)

Starting commit: `b23aca4d293821275d8684fae2677b858275c70f`. The project is now
named `generalized-interval-arithmetic`, with Lean namespace
`GeneralizedIntervalArithmetic` and Lake identifier
`generalized_interval_arithmetic`. This replaces the earlier `IntervalGraphing`
namespace and `interval_graphing` package name. The directory remains
`formalization/lean`; descriptive module names, repository identity, and the PR
branch remain unchanged. Prior dated records above retain the names and logs
actually used in those runs.

Fresh validation from `/workspace/relgraph/formalization/lean`:

- `lake build`: exit 0; all six proof/example modules rebuilt successfully,
  without warnings or errors.
- `lake env lean Audit.lean`: exit 0; all 44 audited declarations are under
  `GeneralizedIntervalArithmetic` and use only
  `[propext, Classical.choice, Quot.sound]`.
- All seven Lean files match the starting commit after only the namespace
  substitution. Proof statements and bodies are otherwise unchanged.
- The dependency lockfile changed only its root package identifier. Toolchain
  and dependency revisions are unchanged.
- `git diff --check`: passed. Application, release, and hosted CI files are
  unchanged; no new assumptions or dependencies were introduced.

New environment-local logs:
`/workspace/lean-tools/generalized-interval-arithmetic-build.log` and
`/workspace/lean-tools/generalized-interval-arithmetic-audit.log`.
No remaining blocker or denied action. This update is for PR #10; no repository
rename or merge is part of the change.

## segment presence milestone (2026-11-06)

Started from merged main commit `158074aaf8df30242efd5b5c40a562bdcacfafd7` on
`feat/segment-presence`. Added `Presence`, `ExpressionContinuity`, and
`PresenceExamples`; `PRESENCE.md` records the exact guarantees and assumptions.

- `lake build`: exit 0. The additional topology dependencies from the existing
  mathlib pin were compiled locally, followed by all three new modules. Final
  output: `Built PresenceExamples`, `Build completed successfully.` No warnings
  or errors remained.
- `lake env lean Audit.lean`: exit 0; all 64 declarations use only
  `[propext, Classical.choice, Quot.sound]`.
- Kernel-checked examples prove a root of `x*x-2` and `(x*x-2)/(x+1)` in
  `[1,2] × {0}`. For `1/x` on `[-1,1] × {0}`, opposite endpoint signs are proved,
  the domain guard rejects the box, and absence of any defined root is proved.
- The specialized presence theorem derives continuity and definedness from
  successful interval evaluation. Only the generic curve theorem takes them as
  explicit premises. Directed rounding uses the existing enclosure contracts;
  it is not assumed continuous.
- `git diff --check`: passed. Existing proof sources, dependency pins, native
  application/build files, and hosted CI are unchanged.

Fresh logs: `/workspace/lean-tools/presence-build.log` and
`/workspace/lean-tools/presence-audit.log`. Real-valued semantic functions are
marked `noncomputable`; interval calculations remain rational and executable.
The pole counterexample required a separate lemma about a defined denominator
to avoid dependent-elimination issues in the proof script; the final proof is
fully checked. No new axiom, placeholder proof, or native-evaluation axiom is
used. No remaining blocker; no merge is authorized for this milestone.

## conservative segment checker milestone (2026-11-06)

Started from `6a00fffa3b6222592ee799db02e60639eb2d2b4b` (PR #11's presence
milestone) on `feat/segment-checker`. This is a reviewable follow-on to that PR,
not a merge of it. Added an executable supplied-segment checker and the
`empty`/`present`/`unknown` classification API.

- `lake build`: exit 0; `PresenceChecker` and `PresenceCheckerExamples` built
  successfully, with no warnings or errors.
- `lake env lean Audit.lean`: exit 0; all 79 audited declarations use only
  `[propext, Classical.choice, Quot.sound]`.
- Audit coverage check: every public theorem in all five presence/continuity/
  checker modules is included in `Audit.lean`.
- Ten kernel-checked controls cover both sign orientations, rational presence,
  positive-constant emptiness, poles, invalid endpoints, endpoint and degenerate
  roots, uncertain signs, and conversion failure.
- `certifySegment_sound`, `classifyWithSegment_empty`, and
  `classifyWithSegment_present` prove the decisive outcomes. The separate
  `empty_disallows_presence` theorem rules out contradictory certificates under
  the same backend contract.
- `git diff --check`: passed. No source uses `sorry`, `admit`, a new axiom, or
  `native_decide`. Dependencies, prior mathematical proofs, application builds,
  and hosted CI are unchanged.

Logs: `/workspace/lean-tools/segment-checker-build.log` and
`/workspace/lean-tools/segment-checker-audit.log`. There are no new FP assumptions:
rounded backends still use only the existing successful finite-conversion
enclosure inequalities. No root-search, completeness, or implementation guarantee
is claimed. No remaining blocker; this milestone is pushed for review without
merge authorization.

## finite candidate search milestone (2026-11-06)

Started from `f0ede151037f1ba59ab9ae99778b2d9c3f7b416b` (PR #12's checker
milestone) on `feat/finite-segment-search`. Added `SegmentSearch` and
`SegmentSearchExamples`; `SEGMENT_SEARCH.md` describes the finite-list API and
optional eight-segment policy. This change is stacked on the unmerged checker
PR, not a merge of the earlier milestones.

- `lake build`: exit 0; both new modules built with no remaining warnings or
  errors. The final output was `Built SegmentSearchExamples` and
  `Build completed successfully.`
- `lake env lean Audit.lean`: exit 0; all 106 audited declarations use no axioms
  beyond `propext`, `Classical.choice`, and `Quot.sound` (some use only `propext`).
- All public theorems in the two new modules are covered by the audit.
- Search proofs cover returned-candidate membership, certification, defined-root
  soundness, exact finite-list success/failure characterization, and append
  priority. Midpoint bounds, generated-endpoint containment, and list length
  eight are proved. Both classifier outcomes have soundness proofs.
- Twelve example theorems include a certified circle, invalid-candidate skipping,
  an empty list, poles, degenerate/shifted boxes, conversion failure, and a
  tangency whose defined root is proved despite an unknown search result.
- `git diff --check`: passed. No new axiom, placeholder proof, or native proof
  shortcut. Existing proofs, dependency/toolchain pins, application/release
  files, and hosted CI remain unchanged.

Logs: `/workspace/lean-tools/segment-search-build.log` and
`/workspace/lean-tools/segment-search-audit.log`. No FP assumptions were added;
midpoint construction uses exact rationals and assumes no machine representability.
No remaining blocker. Subdivision, root-search completeness, and implementation
refinement are outside this bounded milestone; no merge is authorized.

## bounded subdivision milestone (2026-11-06)

Started from `b750c95f4c33eca8767d8ca745556e3b73359b71` (PR #13's finite
search milestone), on `feat/bounded-subdivision`. Added `Subdivision` and
`SubdivisionExamples`; `SUBDIVISION.md` relates this bounded policy to Tupper
§4.2.5–4.2.6 and distinguishes it from a transcription or completeness result.
This milestone is stacked on the still-open PR #13; no prior PR was merged.

- `lake build`: exit 0, with `Built Subdivision`, `Built SubdivisionExamples`,
  and `Build completed successfully.` No remaining warnings or errors.
- `lake env lean Audit.lean`: exit 0. All 130 audited declarations use no axioms
  beyond `propext`, `Classical.choice`, and `Quot.sound`; some use fewer or none.
  Every public theorem in both new modules is included in the audit.
- Thirteen new general theorems cover child containment, exact closed coverage,
  shared boundary membership, defined-root coverage on both axes, sound result
  aggregation and transport, local and recursive classifier soundness, both
  decisive corollaries, and budget-zero behavior.
- Eleven example theorems check absence recovered by subdivision, tangency
  presence recovered at depth three (but not depth one), pole conservatism,
  degenerate boxes, conversion failure, and conservative aggregation. Concrete
  calculations use `decide +kernel`; existence/absence corollaries use the
  general soundness theorems.
- `git diff --check` passed. Source scans found no `sorry`, `admit`, newly
  declared axioms, or `native_decide`. No existing mathematical proof,
  dependency/toolchain pin, native build/release file, or hosted CI was changed.

Logs: `/workspace/lean-tools/subdivision-build.log` and
`/workspace/lean-tools/subdivision-audit.log`. No new FP assumptions or machine
representability requirement. Structural recursion bounds depth and terminates
on degenerate boxes. Unknown remains possible; no completeness, convergence,
performance, root-coordinate, or implementation theorem is claimed. There is no
remaining blocker. This milestone is prepared for review without merging.

## parameter-dependent bounds and domains milestone (2026-11-06)

Started from `56cf5b90866147a4088fdca227270aea79926c70` (PR #14) on
`feat/linear-interval-domains`. Adds `LinearIntervals`, `PartialEnclosures`, and
`GeneralizedExamples`. This PR is stacked for review; none of the open milestones
was merged. The new mathematical modules import ordinary interval foundations,
not the graph-search or subdivision modules.

- `lake build`: exit 0. Final output includes `Built PartialEnclosures`,
  `Built GeneralizedExamples`, and `Build completed successfully.`
- `lake env lean Audit.lean`: exit 0. All 161 audited declarations use only
  subsets of `propext`, `Classical.choice`, and `Quot.sound`. All 10 linear-interval
  theorems, eight partial-enclosure theorems, and 13 new example theorems are
  included. No warnings or errors remain in this build.
- Linear arithmetic proves endpoint-order sufficiency, affine arithmetic
  interpretation, constant/exact embeddings, addition/subtraction inclusion,
  sound hull conversion, and exact affine cancellation.
- Partial-domain contracts prove definite existence, impossible-domain absence,
  definite non-collapse, collapsed-bound absence, restriction, partial addition,
  zero exclusion, and the linear-function bridge. Domain-analysis premises are
  explicit; no automatic domain or continuity analyser is claimed.
- Examples include ordinary versus dependent cancellation, an explicitly
  partial reciprocal, a total jump with opposite signs and no zero, unknown
  domains compatible with both empty and total relations, and composition.
- `git diff --check` passed. All top-level Lean sources were scanned for `sorry`,
  `admit`, `native_decide`, and axiom declarations; none occur. Existing proofs,
  dependency/toolchain pins, native application/release files, and hosted CI
  were not changed.

Logs: `/workspace/lean-tools/generalized-build.log` and
`/workspace/lean-tools/generalized-audit.log`. `GENERALIZED_INTERVALS.md` cites
Tupper §2.9.3, §2.9.7, §2.11, §2.12 and §3.2.18 and explains the exact relationship
and exclusions. Rational linear bounds are implemented; arbitrary functional
bounds and predicate domains are semantic interfaces. No additional FP
assumptions, bit-level claims, or continuity inference is introduced. No remaining
blocker; multiplication/linearization and executable domain analysis remain
future work, rather than incomplete obligations of this milestone.

## linear multiplication milestone (2026-11-06)

Started from `892e35025fbe2297e90d5307baed416b88b26d47` (PR #15), on
`feat/linear-multiplication`. Adds `LinearMultiplication` and
`MultiplicationExamples`; no prior mathematical proof file is edited. The
published stack #11–#15 was verified open/unmerged. `REVIEW_STACK.md` records
incremental bases, original heads, mathematical dependencies, and review focus.

- `lake build`: exit 0; final output includes `Built LinearMultiplication`,
  `Built MultiplicationExamples`, and `Build completed successfully.` No
  remaining warnings or errors.
- `lake env lean Audit.lean`: exit 0. All 182 audited declarations depend only
  on subsets of `propext`, `Classical.choice`, and `Quot.sound`. All eight new
  public general theorems and 13 example theorems are audited.
- General proofs cover join containment, the exact affine-product identity,
  the quadratic correction bound, rational product linearization, real
  four-corner products, linear multiplication enclosure, and all three
  partial-domain soundness obligations for multiplication.
- Examples check sloping square bounds, complementary slopes with hull
  `[0,1/4]` versus ordinary `[0,1]`, constant-factor exactness, sign-crossing
  uncertain operands (including a negative cross-product), and preservation
  of undefinedness under multiplication by zero.
- Finite coefficient computations use `decide +kernel`. All top-level Lean
  sources were scanned: no `sorry`, `admit`, `native_decide`, or axiom
  declarations. `git diff --check` passed.
- Only `formalization/lean` changes. Existing proofs, dependency and toolchain
  pins, native build/release files, and hosted CI remain unchanged.

Logs: `/workspace/lean-tools/linear-mul-build.log` and
`/workspace/lean-tools/linear-mul-audit.log`. `LINEAR_MULTIPLICATION.md` ties the
explicit product policy to Tupper §3.3.1, §3.3.22, and §3.3.25. The uniform
curvature correction and joins are proved sound, not optimal or always tighter
than ordinary intervals. Domain information remains semantic; no new FP
assumptions, continuity inference, generalized expression interpreter, division,
or implementation correctness is claimed. No blocker or substantive unresolved
design decision prevents reviewing this bounded milestone. No PR was merged.

## enforced axiom audit milestone (2026-11-06)

Started from `97c6ddaff3ed1ac800557bd83e9196cc02b80bd9` (PR #16), on
`feat/enforced-axiom-audit`. Earlier records report manual inspection of printed
axiom output; they did not provide build-time enforcement. This milestone adds
that enforcement without rewriting those records or changing proof statements.

- `AuditPolicy` uses Lean's transitive axiom collector and permits exactly
  `propext`, `Classical.choice`, and `Quot.sound`. The 182 named commands now
  fail on any other dependency. A namespace-wide check also passes for all
  391 imported theorem/axiom declarations in `GeneralizedIntervalArithmetic`.
- `Audit` is a default Lake target. `lake build` passed, including enforcement;
  `lake env lean Audit.lean` also passed as a fresh invocation.
- Eight independent-process integration controls passed via
  `python3 -m unittest discover -s tests -v`: axiom-free/allowlisted positives,
  placeholder-proof and transitive-custom-axiom negatives, unlisted namespace
  axiom/placeholder negatives, unknown-name and empty-namespace negatives.
  Invalid fixtures exist only in temporary directories, not imported modules.
- During development an overly broad scan of executable implementation
  declarations rejected a compiler-generated specialization whose dependencies
  included `Nat.cast._at.Rat.instOfNat._spec_1`. The final scope scans theorems
  and axiom declarations and their transitive dependencies, not unused compiler
  implementation artifacts. The allowlist was not expanded. One slow development
  audit was stopped before sharing dependency traversal across namespace roots.
- `git diff --check` passed. No mathematical proof, FP assumption, toolchain or
  dependency pin, native build/release file, or hosted CI was changed.

Logs: `/workspace/lean-tools/enforced-audit-build.log`,
`/workspace/lean-tools/enforced-audit.log`, and
`/workspace/lean-tools/enforced-audit-tests.log`. `AUDIT_POLICY.md` states coverage
and trust limits: unimported modules, other namespaces and unused/private roots
are not automatically audited. Definitions used by checked proofs are traversed.
The checker is tooling based on the pinned Lean implementation, not a new axiom
or a formal verification of that implementation. No remaining blocker; no merge.

## shared-parameter expression interpreter milestone (2026-11-06)

Started from `602ddb82de853b5854c78faff124706fa8a024b5` (PR #17), on
`feat/linear-expression-evaluator`. Adds `LinearEvaluator` and
`LinearEvaluatorExamples`, reusing `Expr`, `Value`, and the proved linear
operations. No old mathematical proof file or audit policy is changed.

- `lake build`: exit 0, including the enforced audit. Both new modules build
  without remaining warnings/errors. A fresh `lake env lean Audit.lean` also
  passes: 200 named landmarks and 417 imported theorem/axiom declarations in
  the project namespace obey the exact three-axiom allowlist.
- All five new general theorems and 13 example theorems have named audit entries;
  the namespace check additionally covers generated theorem declarations and
  transitive dependencies. The audit's eight independent-process controls
  passed in PR #17; unchanged audit policy/tests were not redundantly rerun here.
- `evalLinear_sound` proves enclosure against existing partial `Value` semantics.
  `evalLinear_defined` independently proves existence of an actual semantic value
  from success. Two bridge theorems establish the full partial-enclosure contract
  on `[0,1]` and retain an explicit parameter-domain restriction.
- Kernel-checked calculations establish exact cancellation, correlated sum
  cancellation, and the `[0,1/4]` complementary product enclosure. Further proofs
  supply semantic existence/enclosure and a restricted-domain contract.
- A defined `1/1` expression returns unsupported/unknown, with its value 1 proved
  separately. Zero times a division-by-zero expression also returns unsupported;
  the interpreter does not erase unsupported subexpressions algebraically.
- `git diff --check` passed. New proof sources contain no placeholder proof,
  declared axiom, or native proof shortcut. Dependency/toolchain pins, native
  build/release files, and hosted CI are unchanged.

Logs: `/workspace/lean-tools/linear-evaluator-build.log` and
`/workspace/lean-tools/linear-evaluator-audit.log`. `LINEAR_EVALUATOR.md` states
that this is an exact rational polynomial fragment with real semantics, not
linear division, automatic coordinate-domain inference, continuity tracking,
optimal range analysis, or machine implementation verification. Explicitly
restricted coordinate domains remain caller supplied. No additional FP
assumptions or new blocker. The audit and interpreter milestones are separate
reviewable PRs; no merge was performed.

## guarded linear reciprocal/division milestone (2026-11-06)

Started from `22817a358800c7dc65df3b4fc386d42a1a218621` (PR #18), on
`feat/guarded-linear-division`. Added standalone `LinearDivision` and
`DivisionExamples`; the interpreter and audit policy under independent review
are unchanged.

- `lake build` and fresh `lake env lean Audit.lean`: exit 0. Enforced audits
  passed for 218 named landmarks and 450 imported namespace theorem/axiom
  declarations. No warnings/errors remain.
- All six new public general theorems and 12 examples have named audit entries.
  Proofs cover guard success, nonzero denominators, reciprocal/quotient
  enclosure, and the three partial-domain contract obligations.
- Kernel coefficient controls cover positive/negative reciprocal bounds,
  numerator dependence retained in a quotient, exact constants, zero/spanning/
  touching-zero denominators, and zero numerator without guard bypass.
  Additional semantic controls distinguish failed guards from undefinedness
  and preserve punctured operand domains after successful numerical guarding.
- `git diff --check` passed. New source scans found no proof placeholders,
  declared axioms, or native proof shortcuts. Pins, native build/release files,
  hosted CI, old mathematical proofs, and FP assumptions are unchanged.

Logs: `/workspace/lean-tools/linear-division-build.log` and
`/workspace/lean-tools/linear-division-audit.log`. `LINEAR_DIVISION.md` relates
this conservative constant-bound fallback to Tupper §2.9.4, §3.3.16, and §3.3.27.
Denominator dependence is forgotten for the reciprocal; the policy is sound,
not optimal. It does not infer or use domain predicates to bypass the whole-hull
zero guard and does not add division to expression interpretation. A separate
domain-local interpreter bridge addresses the independent review's domain-local
premise observation. No blocker or new substantive decision required; no merge.

## domain-local interpreter contract milestone (2026-11-06)

Started from `e8b4d033f1947f09c695d56def122b491b2e8f43` (PR #19), on
`feat/domain-local-evaluator`. Adds `DomainEvaluator` and
`DomainEvaluatorExamples` to address the independent review's observation about
#18's sufficient whole-range enclosure premise. Old theorems and interpreter
behavior are unchanged.

- `lake build` and fresh `lake env lean Audit.lean`: exit 0. Enforced checks
  passed for 231 named landmarks and 469 imported namespace theorem/axiom
  declarations. No remaining warnings or errors.
- Both new general theorems and all 11 example theorems have named audit entries.
  `evalLinear_relational_sound` proves all three domain-contract clauses from
  partial coordinate relations; `evalLinear_local_sound` requires function
  enclosure only on the explicitly supplied domain within `[0,1]`.
- A representative that is 7 at an excluded parameter and 0 elsewhere formally
  fails whole-range enclosure by the zero interval, yet satisfies the local
  bridge. This witnesses a real relaxation of the earlier premise.
- Other controls prove absence at an excluded coordinate parameter, existence
  inside the domain, and preservation of unknown domain information for an empty
  coordinate relation. No continuity or root-existence premise is inferred.
- `git diff --check` passed. New source scans found no placeholder proofs,
  declared axioms, or native proof shortcuts. Audit policy and its already-passed
  independent-process controls are unchanged. Pins, native build/release files,
  hosted CI, and FP assumptions are unchanged.

Logs: `/workspace/lean-tools/domain-evaluator-build.log` and
`/workspace/lean-tools/domain-evaluator-audit.log`. `DOMAIN_EVALUATOR.md` relates
the semantic domain distinction to Tupper §2.11 and states the intentional strict
environment scope: both coordinate bindings must exist, rather than performing
minimal free-variable domain analysis. The interface is not automatic domain
inference or a new division interpreter. There is no unresolved design decision
or blocker for this bounded contract extension. No PR was merged.

## guarded arithmetic/interpreter integration milestone (2026-11-06)

Started from `d6355f047026cd93bbfdf2a67524c16bf21912cc` (PR #20), on
`feat/guarded-expression-evaluator`. The integration gap was that standalone
quotient bounds did not participate in expression evaluation. Added
`GuardedEvaluator` and `GuardedEvaluatorExamples`; no existing mathematical proof
module or audit policy was edited.

- Clean `lake build` and fresh `lake env lean Audit.lean`: exit 0. Enforced
  checks pass for 255 named landmarks and 512 imported namespace theorem/axiom
  declarations, under the unchanged three-axiom allowlist. No remaining warnings
  or errors in the final build.
- All five new public general theorems and 19 example theorems are named checks.
  Soundness and local definedness are proved separately; definedness constructs
  every denominator value and derives nonzero from the guard before using
  `Value.div`. Exact preservation of prior successful polynomial results is
  proved, followed by relational and domain-local contracts.
- Integration controls include nested reciprocals, retained numerator
  dependence, safe constant division, boundary and cancellation poles, and zero
  multiplication without bypassing a pole. A direct `Value` construction verifies
  a quotient independently of the interpreter's definedness theorem.
- A counterexample proves that success on the certified input model does not
  imply global definedness. A second semantic witness shows an inconclusive
  pole-touching box can still have defined interior values. Partial environment
  examples prove exclusion and existence at appropriate parameters.
- The eight independent-process audit controls were rerun and passed, including
  rejection of placeholder proofs and transitive custom axioms. These controls
  remain temporary fixtures, not project proof dependencies.
- `git diff --check` passed. New proof sources contain no placeholders, axiom
  declarations, or native proof shortcuts. Dependency/toolchain pins, native
  build/release files, hosted CI, and FP assumptions remain unchanged.

Logs: `/workspace/lean-tools/guarded-evaluator-build.log`,
`/workspace/lean-tools/guarded-evaluator-audit.log`, and
`/workspace/lean-tools/guarded-evaluator-audit-controls.log`.
`GUARDED_EVALUATOR.md` explicitly distinguishes polynomial global definedness
from guarded local definedness and records the strict two-coordinate environment,
separate unary relation, and whole-hull guard limits. Domain predicates do not
sharpen numerical guards; no completeness, continuity, root-existence, optimality,
or machine-correctness claim is made. No new decision requiring John or blocker
was identified. No merge was performed.

## piecewise domain selection milestone (2026-11-06)

Started from `df548a08a9f1118ab2edd5355877e378d324e5b1` (PR #21), on
`feat/piecewise-domain-selection`. Added `PiecewiseSelection` and
`PiecewiseExamples` as a bounded value/domain operator and compositional bridge;
existing interpreters, arithmetic proofs, and continuity/presence proofs are
unchanged.

- `lake build` and fresh `lake env lean Audit.lean`: exit 0, with no warnings or
  errors. Enforced allowlisting passes for 280 named landmarks and 558 imported
  namespace theorem/axiom declarations.
- All three new public general theorems and 22 example theorems have named audit
  entries. General proofs establish the strict rational threshold classifier,
  all three partial-domain selection obligations, and composition of successful
  guarded branch interpretations.
- Decision controls cover true, equality-false, lower-bound false, upper-bound
  unknown, and an interior threshold. Value bounds and decisions are computed
  with kernel reduction. The unknown-domain rule preserves possibility while
  requiring both branches for definite existence.
- Independent semantic controls prove a selected jump is enclosed, has opposite
  endpoint signs, has no zero, and is not continuous on `[0,1]`. The last result
  uses the pre-existing intermediate-value theorem as a contradiction argument;
  it is not a continuity assumption derived from the new selection contract.
- Separate controls establish existence with an undefined inactive branch,
  absence with an undefined active branch, unresolved partial-domain metadata,
  and the bridge from actual guarded interpreter outputs.
- `git diff --check` passed. New source scans found no placeholders, axiom
  declarations, or native proof shortcuts. The audit policy and its #21-validated
  independent-process controls are unchanged. Pins, native build/release files,
  hosted CI, and FP assumptions are unchanged.

Logs: `/workspace/lean-tools/piecewise-build.log` and
`/workspace/lean-tools/piecewise-audit.log`. `PIECEWISE_SELECTION.md` relates the
bounded specialization to Tupper §2.9.2, §2.12, and §3.3.18. The guard predicate
is total; automatic partial guards, maximal-domain inference, a conditional Expr
constructor, and lazy evaluation of failing branches are not implemented.
The guarded-branch integration requires both branch interpretations to succeed;
the general semantic contract separately supports an empty-domain inactive
branch. No continuity certificate, root claim, or new FP assumption is added.
No blocker or decision requiring John; no merge performed.

## conditional expression tree milestone (2026-11-06)

Started from `91db4d70ba67e79708e7e2c1d206af71a64ba830` (PR #22), on
`feat/conditional-expression-trees`. Added `ConditionalEvaluator` and
`ConditionalExamples`; old Expr, evaluators, and selection contracts are unchanged.

- Full `lake build` and fresh `lake env lean Audit.lean`: exit 0, no warnings or
  errors. The unchanged allowlist passes 312 named checks and 607 imported
  namespace theorem/axiom declarations. All nine new general theorems and 23
  public example theorems have named checks.
- Proofs establish local enclosure and definedness, exact leaf compatibility,
  pointwise guard certificates, inactive-branch independence, and all three
  partial-coordinate contract obligations for the finite conditional tree.
- Kernel computations and independent semantic constructions cover certified
  choices skipping actual poles, equality choosing false, active poles,
  undefined guards with identical branches, and nested inactive bad guards.
- A reciprocal guard succeeds on certified inputs but has no semantic value
  outside them at its pole. An unresolved partial tree has a constructed value
  at one point and no value at another; interpreter failure is not undefinedness.
- An unresolved total jump gets joined bounds and is connected to the existing
  discontinuity result. A punctured coordinate environment retains exclusion
  and interior existence after successful selection.
- `git diff --check` passed. Both new proof sources contain no placeholders,
  axiom declarations, or native proof shortcuts. Audit policy and its previously
  validated independent-process controls, dependency/toolchain pins, native
  build/release files, hosted CI, and FP assumptions remain unchanged.

Logs: `/workspace/lean-tools/conditional-build.log` and
`/workspace/lean-tools/conditional-audit.log`. `CONDITIONAL_EVALUATOR.md` records
thesis links and scope: arithmetic guards/leaves, nested conditional branches,
local definedness, strict complete-coordinate environments, and no domain-based
numerical guard refinement. Unknown decisions still require both interpretations.
Inactive-branch independence concerns the Lean evaluator definition, not native
compiler/runtime costs. No continuity, root, maximal-domain, completeness, or FP
implementation claim is made. No blocker or decision requiring John; no merge.

## conditional arithmetic composition milestone (2026-11-06)

Started from `3adad1af5e7546842701bfc94ef1a5fe4ccf1361` (PR #23), on
`feat/conditional-arithmetic-composition`. Added ConditionalArithmetic and
ConditionalArithmeticExamples, leaving previous syntax and interpreters intact.

- Full `lake build` and fresh `lake env lean Audit.lean`: exit 0, no warnings or
  errors. The unchanged allowlist passes 340 named checks and 665 imported
  namespace theorem/axiom declarations. All nine new general theorems and 19
  public example theorems have named checks.
- Generic leaf-map and binary-distribution semantic equivalences are proved.
  Their explicit transformation premises are discharged for addition,
  subtraction, multiplication, and nonzero-guarded division by Value constructor
  proofs. Concrete exact value/domain preservation adds no unproved premise.
- Local enclosure, definedness, and relational domain contracts are transferred
  through that equivalence. Leaf compatibility with evalGuarded is exact.
- Kernel checks cover all four operations on certified conditional operands with
  inactive poles. Separate semantic proofs verify strict undefinedness for zero
  multiplication on either side and division by zero.
- Branchwise reciprocal evaluation of a sign-changing jump succeeds; a separate
  computation proves that joining the denominator first returns unknown.
  A direct semantic witness is constructed at every real coordinate.
- A correlated repeated-guard quotient has a directly constructed semantic value
  1/2 everywhere, yet evaluation is proved unknown. This exposes unresolved
  inconsistent paths and prevents a completeness claim.
- `git diff --check` passed. Both new proof sources were scanned for placeholders,
  axiom declarations, and native proof shortcuts; none occur. Audit policy and
  its previously validated negative controls, dependency/toolchain pins, native
  build/release files, hosted CI, and FP assumptions remain unchanged.

Logs: `/workspace/lean-tools/conditional-arithmetic-build.log` and
`/workspace/lean-tools/conditional-arithmetic-audit.log`.
CONDITIONAL_ARITHMETIC.md records the precise relation to the previously read
thesis syntax/partial-function/conditional-specialization material. Fresh web
retrieval of the two syntax/optimization pages failed with tool internal errors;
no new claim depends on that unavailable retrieval.

The representation distributes trees without sharing or path-condition
refinement. Conditional-valued guards, a full new surface AST, efficiency,
continuity, root existence, maximal domains, and FP implementation correctness
are outside scope. No implementation blocker or decision requiring John was
identified. No merge was performed.

## integrated assessment and verification (2026-11-06)

Started from #24 at `2f98daf614c14a44b5a32b7247ff13feae083605`, on
`chore/lean-integration-assessment`. This increment adds assessment and local
verification tooling, not another arithmetic operation or changed theorem API.

- GitHub metadata confirmed #11–#24 open, unmerged, and mergeable. Remote heads
  and bases match the local 14-commit linear chain from main `158074a`.
  The cumulative diff is confined to formalization/lean.
- Compiler dependency output confirms all 36 root modules are registered in
  Lake, default-built, and reachable from Audit. No existing omission was found.
- The original eight audit process controls were rerun independently: all passed
  (11.403s), including rejection of placeholders and transitive/custom axioms.
- The new `./check.sh` completed with exit 0: default Lake build, fresh standalone
  Audit invocation, and all 13 Python tests (36.541s for the test phase).
  Build/audit output contains no warnings or errors. Existing cumulative library
  totals remain 340 named checks and 665 namespace theorem/axiom declarations;
  the policy and proof libraries are unchanged.
- New project controls use Lean's `--deps`, test inventory/default-target/audit
  reachability, and verify synthetic omissions are rejected. Their scope is the
  current flat library layout; test fixtures are handled separately.
- `tests/Integration.lean` was also checked directly in a fresh Lean process:
  exit 0, no warnings/errors, 22 declarations in its own enforced namespace
  audit. It contains 14 public regression theorems and imports implementation
  modules rather than milestone example fixtures.
- Fresh instances link computed subdivision emptiness to absence, guarded
  quotient presence to an actual defined root, nested conditional arithmetic
  bounds to nonzero values and local definedness, and a restricted coordinate
  contract to boundary absence and interior existence. A pole remains unknown.
- `git diff --check` and proof-source scans passed. No placeholders or native
  proof shortcuts occur in the new Lean fixture. Intentionally invalid audit
  fixtures remain temporary subprocess inputs, never library dependencies.

Logs: `/workspace/lean-tools/consolidation-audit-controls.log`,
`/workspace/lean-tools/consolidation-integration.log`, and
`/workspace/lean-tools/consolidation-check.log`.

INTEGRATION_ASSESSMENT.md records the coverage matrix, semantic boundaries,
redundant abstractions, merge/retargeting risks, and prioritized recommendation:
review/consolidate first, then prove parameter restriction/reparameterization
and coverage before expanding conditional syntax. Thesis contents and relevant
linear/functional/domain/property/discontinuity/interval-set/continuity-testing
sections were successfully read afresh; no formula-image encoding was inferred.
This is source inspection and independently constructed regressions, not a claim
of independent human review or verification of the Lean implementation. No
blocking interface defect was found; executable domain analysis and generalized
continuity tracking remain gaps. No FP assumptions, dependency pins, native
build/release files, hosted CI, merges, or history rewrites were introduced.

## parameter restriction and supplied coverage (2026-11-06)

Started from #25 at `8f6a7b45a5056d986d96d099994fa9b30b811d2f`, on
`feat/parameter-restriction`. Added ParameterRestriction and its examples without
changing existing arithmetic, semantics, subdivision, or audit policy.

- `./check.sh`: exit 0. Full Lake build and fresh standalone Audit passed with
  no warnings/errors: 372 named checks and 728 imported namespace theorem/axiom
  declarations. All nine new general and 23 public example theorems are named.
- All 13 Python tests passed (46.175s): audit acceptance/rejection controls,
  inventory/default-build/audit reachability for all 38 root modules, negative
  coverage controls, and the independent end-to-end fixture.
- Exact affine composition, containment equivalence, cell surjectivity including
  zero width, all three domain-contract obligations, and guarded relational
  interpretation under transported coordinates are kernel checked.
- The supplied-cover transfer theorem is tested with the old lower/upper halves,
  reusing split_cover and split_boundary. No subdivision algorithm is copied.
- Kernel computations distinguish reciprocal success on [1/2,1] from unknown on
  the original range and on the zero-touching left half; a point cell gives the
  exact reciprocal. Actual local definedness follows from evaluator success.
- An explicit domain hole at the common midpoint stays absent from both cells;
  the right-cell interpreter's sound contract proves absence at its boundary and
  existence at an interior parameter. A point cell at the hole has no possible
  domain despite a numerically successful operation. Strict left-boundary guard
  uncertainty remains unknown. A positivity claim from cell interpretation is
  transferred to the entire original range only through proved coverage.
- `git diff --check` passed. New proof sources contain no placeholders, custom
  axioms, or native proof shortcuts. The allowlist, pins, native build/release,
  hosted CI, and FP assumptions remain unchanged.

Logs: `/workspace/lean-tools/parameter-core.log`,
`/workspace/lean-tools/parameter-examples.log`, and
`/workspace/lean-tools/parameter-check.log`.
PARAMETER_RESTRICTION.md gives the API, exact premises, and thesis relationship.
The relevant parameter-mapping/domain sections were read successfully via the
thesis contents links after direct page opens returned tool internal errors.
Closed rational cells and a proved supplied finite cover are explicit choices;
there is no cover inference, open-boundary treatment, interval-set evaluator,
continuity certificate, maximal-domain claim, or commuting-nonlinear-evaluation
claim. No semantic design blocker was encountered and no merge was performed.

## defined arithmetic continuity bridge (2026-11-06)

Started from #26 at `796cc60d733c0e287cd87cc013d51ea2cd00b200`, on
`feat/defined-arithmetic-continuity`. Added SemanticContinuity and its examples;
existing expressions, evaluator definitions, ordinary continuity proofs, and
parameter/domain contracts are unchanged.

- `./check.sh`: exit 0. Full build and fresh standalone Audit passed without
  warnings/errors: 389 named checks and 754 imported namespace theorem/axiom
  declarations. All five new general and 12 public example theorems are named.
- All 13 tests passed (39.431s), including axiom rejection controls, inventory/
  default-build/audit coverage for all 40 root modules, and the independent
  end-to-end fixture.
- The semantic theorem proves relative continuity for the current arithmetic
  Expr from continuous coordinates and actual definedness on the supplied set.
  Nonzero division premises are extracted from Value constructors and connected
  to the pre-existing canonical realValue through value_eq_realValue.
- Guarded evaluation supplies local definedness, and the restricted-cell
  corollary uses exact reparameterization plus the existing affine segment
  continuity theorem. No new continuity certificate data type is introduced.
- A dependency-sensitive quotient is unknown under ordinary interval evaluation
  but succeeds under the linear evaluator. Its new continuity/Value certificate
  combines with exact endpoint bounds and the existing IVT theorem to prove an
  actual partial-semantic root. No classifier implementation is altered.
- A reciprocal is certified continuous on the restricted right cell, while a
  separate proof rejects semantic definedness at original coordinate zero.
- A punctured reciprocal has directly constructed semantic values and relative
  continuity on its punctured domain, opposite endpoint signs, no defined zero
  anywhere, and no semantic value at the midpoint. Thus relative continuity
  cannot silently become the full-interval IVT premises.
- `git diff --check` and proof-source scans passed: no placeholders, new axioms,
  or native proof shortcuts. The audit policy, pins, native application build/
  release files, hosted CI, and FP assumptions are unchanged.

Logs: `/workspace/lean-tools/semantic-continuity-core.log`,
`/workspace/lean-tools/semantic-continuity-examples.log`, and
`/workspace/lean-tools/semantic-continuity-check.log`.
SEMANTIC_CONTINUITY.md relates the bounded rule to freshly read thesis §2.12 and
§3.3.18 and states the limits: no arbitrary-relation or conditional continuity,
no cross-cell gluing, no automatic domain/property analyzer, and no assertion
that chosen coordinate representatives belong to a partial environment at its
holes. No semantic design blocker was encountered. No merge was performed.

## finite closed-cell continuity composition (2026-11-06)

Started from #27 at `58693da381567f2ce8f2b8f60fca720c724974c4`, on
`feat/closed-cell-continuity`. Added CellContinuity and its examples using the
existing ParameterCell, ParameterCover, semantic continuity, and IVT interfaces.

- `./check.sh`: exit 0. Full build and fresh standalone Audit passed without
  warnings/errors: 404 named checks and 790 imported namespace theorem/axiom
  declarations. All three new general and 12 public example theorems are named.
- All 13 tests passed (39.168s), including forbidden-axiom process controls,
  module inventory/default-build/audit reachability for all 42 root modules,
  negative coverage controls, and the independent integration fixture.
- Cell continuity equivalence handles positive-width affine inversion and the
  singleton case separately. Finite closed-union continuity reuses mathlib's
  ContinuousOn.union_isClosed; the common-function and agreement premises are
  explicit, including endpoints and every overlap.
- A rational expression's whole-range generalized evaluation is proved unknown,
  while both closed halves succeed. Existing local certificates yield global
  continuity via the new theorem and actual global Value witnesses via the old
  coverage pullback. The existing IVT theorem then yields a defined root.
- Negative controls prove that independently continuous constants with different
  boundary values admit no common agreeing representative; a geometric gap
  fails ParameterCover; and a semantic pole prevents full local Value
  certification despite geometric coverage. Point cells and shared-boundary
  values are explicitly exercised.
- `git diff --check` and new-source scans passed. No placeholders, custom axioms,
  or native proof shortcuts. Existing semantics, evaluators, coverage and
  subdivision definitions, axiom policy, pins, native build/release, hosted CI,
  and FP assumptions are unchanged.

Logs: `/workspace/lean-tools/cell-continuity-core.log`,
`/workspace/lean-tools/cell-continuity-examples.log`, and
`/workspace/lean-tools/cell-continuity-check.log`.
CELL_CONTINUITY.md relates this bounded composition rule to the previously read
thesis property/continuity material and states its side conditions. No automatic
branch matching, cover construction, infinite closed-cover result, numerical
property analyzer, or maximal-domain claim is added. Continuity of a total
representative and actual partial-semantic definedness remain separate. No
blocking design uncertainty was encountered. No merge was performed.

## matching-threshold conditional continuity (2026-11-06)

Started from #28 at `6cfa21c15d6743275ea103b4bbc7860e290c36d3`, on
`feat/threshold-conditional-continuity`. Added ConditionalContinuity and examples,
reusing existing ConditionalValue and finite closed-cover composition.

- `./check.sh`: exit 0. Full build and fresh standalone Audit passed without
  warnings/errors: 419 named checks and 825 imported namespace theorem/axiom
  declarations. Both new general and all 13 public example theorems are named.
- All 13 tests passed (49.514s): axiom rejection controls, inventory/default-build/
  audit reachability for all 44 root modules, negative coverage controls, and the
  independent integration fixture.
- The rule explicitly requires an actual guard Value equal to the parameter,
  rational threshold bounds, continuous branch representatives on the closed
  sides, matching boundary values, and actual branch values only where active.
  Equality selects the false branch. The true branch need not have a value at
  the threshold if its supplied continuous extension matches the false branch.
- The removable-singularity conditional is proved continuous and defined
  everywhere on the unit range, while a separate proof rejects the true branch's
  boundary value. The existing interpreter is proved unknown on that same tree;
  no automatic continuity analysis is claimed.
- A matching nonconstant V-shaped representative is continuous. Unmatched jump,
  active boundary pole, and undefined guard controls preserve the required
  distinctions and reject missing semantic evidence.
- The requested #28 positive agreement-wrapper regression uses distinct local
  affine functions on cells overlapping over [1/4,3/4]. Full-cell algebraic
  identities, not endpoint samples, establish agreement with the common global
  function and feed the existing wrapper theorem. Distinctness is checked too.
- `git diff --check` and source scans passed: no placeholders, custom axioms, or
  native proof shortcuts. Existing evaluator/gluing interfaces, policy, pins,
  native build/release, hosted CI, and FP assumptions are unchanged.

Logs: `/workspace/lean-tools/conditional-continuity-core.log`,
`/workspace/lean-tools/conditional-continuity-examples.log`, and
`/workspace/lean-tools/conditional-continuity-check.log`.
CONDITIONAL_CONTINUITY.md records the sufficient rule and its relation to the
previously read thesis property/continuity framework. Guard equality, continuous
extensions, and boundary matching remain supplied proofs; arbitrary crossings,
external coordinate-environment membership, automatic limits/property analysis,
and maximal domains are not inferred. No design blocker was encountered and no
merge was performed.

## Finite linear covers (2026-11-06)

Based on #29 (`013c2c6`), branch `feat/finite-linear-covers`.

- Final `./check.sh` exited 0: full Lake build, standalone enforced audit, and
  all 13 Python integration/enforcement tests (43.787 seconds). No warnings or
  errors in the final log. The audit passed 440 named checks and 859 imported
  namespace theorem/axiom declarations; all 46 root modules are registered and
  reachable. The standard allowlist remains `propext`, `Classical.choice`, and
  `Quot.sound`.
- All seven public core theorems and fourteen public example theorems receive
  named audits. Kernel-checked concrete decisions compare separate versus
  joined reciprocal behavior and reject a zero component. Arithmetic evaluation
  feeds both constant and varying branch covers; separate witnesses establish
  actual values and nonzero-denominator reciprocal values for the varying case.
- Empty/nonempty controls demonstrate that `Covers` alone supplies no existence
  or continuity claim. Reciprocal traversal preserves every input component on
  success, and its semantic conclusion uses explicit partial quotient values.
- `git diff --check` and new-source placeholder/custom-axiom/native-shortcut
  scans passed. No dependencies, existing interpreter behavior, app build,
  hosted CI, or floating-point assumptions changed.

Final log: `/workspace/lean-tools/finite-cover-final-check.log`.
Focused example build: `/workspace/lean-tools/finite-cover-examples.log`.
The earlier `/workspace/lean-tools/finite-cover-check.log` is superseded: two
existence examples were added during that run, so its standalone audit found
stale compiled declarations. The final run rebuilt them and passed every check.
The thesis interval-set source was reread through its contents link after a
transient direct-page lookup error. No unresolved blocker or merge.

## Conditional cover/domain integration (2026-11-06)

Based on #30 (`f409ade`), branch `feat/conditional-cover-domains`.

- `./check.sh` exited 0: full Lake build, fresh standalone enforced audit, and
  all 13 Python integration/enforcement tests (41.704 seconds). No warnings or
  errors in the final log. All 48 root modules are registered and audit-reachable.
- Audit passed 468 named checks and 902 imported namespace theorem/axiom
  declarations. All eight public core and twenty public example theorems have
  named audits. The allowlist remains exactly `propext`, `Classical.choice`,
  and `Quot.sound`; neither enforcement nor its negative fixtures changed.
- The cover interpreter's success flag is proved equal to the scalar
  interpreter's for all trees and inputs. Actual-value enclosure is proved
  separately, and definedness reuses the existing theorem via that equivalence.
- The relational interpreter contract carries enclosure, possible definedness,
  and definite definedness. Guarded finite-cover reciprocation preserves all
  three with explicit nonzero evidence extracted from enclosing components.
- The jump regression composes interpretation, zero exclusion, reciprocation,
  and domain proofs. A punctured coordinate environment stays punctured, with
  definite reciprocal values on both sides. The expression itself is proved
  defined at the excluded environment parameter. Scalar reciprocation fails.
- Kernel-checked controls retain lazy true/equality-false choices, unresolved
  branch failure, undefined-guard failure, and zero-denominator rejection.
  Separate actual-value proofs demonstrate that unknown need not mean undefined.
  The discontinuity control retains the previously established jump theorem.
- `git diff --check` and new-source placeholder/custom-axiom/native-shortcut scans
  passed. No syntax, existing scalar evaluator, pins, app build/release, hosted
  CI, or FP assumptions changed. No merge or unresolved blocker.

Logs: `/workspace/lean-tools/conditional-cover-examples.log` and
`/workspace/lean-tools/conditional-cover-check.log`. Initial focused builds had
ordinary elaboration failures (explicit case equation, cast normalization and
pattern-variable naming), corrected before the successful focused and full
runs. CONDITIONAL_COVERS.md documents the conservative coordinate-domain
intersection, absence of continuity inference and unverified resource bounds.

## Domain-certified finite-cover presence (2026-11-06)

Based on #32 (`37e6dd5`), branch `feat/domain-certified-cover-presence`.

- Final `./check.sh` exited 0: Lake build, standalone enforced audit, and all
  13 Python integration/enforcement tests (50.502 seconds). No warnings/errors
  in the final log. All 50 root modules are registered and audit-reachable.
- Audit passed 484 named checks and 926 imported namespace theorem/axiom
  declarations. All three public core and thirteen public example theorems have
  named audits. The allowlist remains exactly `propext`, `Classical.choice`,
  and `Quot.sound`; no audit policy or negative fixture changes.
- Conditional-value uniqueness is proved from existing arithmetic semantics,
  including agreement of guard values. Finite-cover domain restriction retains
  both domain directions and the actual-value enclosure obligation.
- The presence theorem requires continuous representative agreement, definite
  membership over the whole unit path, and signs for every cover component at
  the endpoints. It extracts an actual relational zero after IVT, rather than
  inferring relation membership from a representative's zero.
- A two-slope conditional composes the existing threshold continuity theorem,
  actual conditional values, finite-cover evaluation, coordinate-domain soundness,
  semantic uniqueness, and rational sign checks into an actual-root certificate.
- Restricting the same relation to omit the unique zero retains the cover,
  representative, endpoint values and signs, but has no relational root. The
  missing whole-path definite-domain premise is explicitly refuted.
- `git diff --check` and placeholder/custom-axiom/native-shortcut scans passed.
  No existing evaluator, syntax, dependency pins, app build/release, hosted CI,
  or FP assumptions changed. No merge or unresolved blocker.

Final log: `/workspace/lean-tools/cover-presence-final-check.log`.
Focused successful build: `/workspace/lean-tools/cover-presence-examples.log`.
The earlier `cover-presence-check.log` predates the new audit registration and
is not evidence for auditing these new declarations; the complete check was
rerun after registration. Initial focused elaboration errors were corrected
before validation. COVER_PRESENCE.md records all supplied hypotheses, the
single-valued-representative restriction, and conservative sign conditions.

## Finite-cover inclusion and coalescing (2026-11-06)

Based on #33 (`c7264ff`), branch `feat/finite-cover-coalescing`.

- `./check.sh` exited 0: full Lake build, fresh standalone enforced audit, and
  all 13 Python integration/enforcement tests (45.077 seconds). No warnings or
  errors in the final log. All 52 root modules are registered and audit-reachable.
- Audit passed 514 named checks and 971 imported namespace theorem/axiom
  declarations. All fifteen public core and fifteen public example theorems
  receive named audits. The allowlist remains exactly `propext`,
  `Classical.choice`, and `Quot.sound`; enforcement and negative fixtures remain
  unchanged.
- Semantic cover inclusion transports both bare enclosure and the unchanged
  domain contract. Singleton soundness is proved equivalent to the existing
  scalar partial-enclosure interface.
- Coalescing includes every input represented value on the unit parameter range.
  Successful limit output has length at most the requested capacity and retains
  the same SoundOn contract. Positive capacities succeed; zero rejects nonempty
  covers as unknown, while empty covers remain empty.
- End-to-end conditional/limit composition preserves the coordinate-domain hole
  and definite-value witnesses. Strict range information loss is proved with a
  spurious zero and refuted reverse inclusion; reciprocal success becomes unknown
  after coalescing, without altering actual-value semantics.
- An independent three-component calculation checks sloping output coefficients
  and the all-or-one policy. The earlier two-slope conditional's actual-root
  certificate is re-established with the coalesced contract and endpoint signs.
- `git diff --check` and new-source placeholder/custom-axiom/native-shortcut scans
  passed. No interpreter default, expression syntax, pins, app build/release,
  hosted CI or FP assumptions changed. No merge or unresolved blocker.

Logs: `/workspace/lean-tools/cover-coalescing-examples.log` and
`/workspace/lean-tools/cover-coalescing-check.log`. A focused initial build's
unnecessary-simpa warning was corrected before the successful final runs.
COVER_COALESCING.md records the freshly reviewed thesis §2.13.1 motivation,
semantic-only inclusion relation, explicit size policy and precision tradeoff.
The proved bound concerns returned list length only, not time, peak memory,
intermediate covers or recursion. No resource-accounting claim is made.

## Finite-cover parameter restriction (2026-11-06)

Based on #34 (`7ba5b92`), branch `feat/finite-cover-restriction`.

- `./check.sh` exited 0: full Lake build, fresh standalone enforced audit, and
  all 13 Python integration/enforcement tests (44.703 seconds). No warnings or
  errors in the final log. All 54 root modules are registered and audit-reachable.
- Audit passed 540 named checks and 1,025 imported namespace theorem/axiom
  declarations. All five public core and twenty-one public example theorems
  receive named audits. The allowlist remains exactly `propext`,
  `Classical.choice`, and `Quot.sound`; no enforcement changes.
- Exact represented membership and component count are proved under componentwise
  reuse of LinearInterval.reparam. Inclusion and both domain directions transport
  through the existing cell map and pullDomain, with explicit local unit range.
- A bridge reuses the existing conditional cover evaluator on restricted
  coordinate enclosures and the same pulled-back partial coordinate relations.
  No second cell representation, subdivision policy or evaluator was introduced.
- An independent genuinely multivalued relation (t or 1-t) gives exact coefficient
  checks for restricting before versus after coalescing. A spurious represented
  value refutes reverse inclusion. Only the finer result passes the reciprocal
  guard; its domain contract and actual reciprocal existence are proved.
- Two distinct actual values explicitly refute a single representative agreeing
  with the relation, preventing blind application of #33's presence premise.
- A degenerate cell at a domain hole has no actual values despite nonempty
  numerical bounds. Fresh right-cell conditional evaluation selects one branch,
  while direct reparameterization retains two. The boundary hole remains absent
  and the interior is definitely defined.
- `git diff --check` and new-source placeholder/custom-axiom/native-shortcut scans
  passed. No existing evaluator behavior, syntax, pins, app build/release, hosted
  CI or FP assumptions changed. No merge or unresolved blocker.

Logs: `/workspace/lean-tools/cover-restriction-core.log`,
`/workspace/lean-tools/cover-restriction-examples.log`, and
`/workspace/lean-tools/cover-restriction-check.log`.
COVER_RESTRICTION.md relates the work to the freshly reviewed thesis linear
interval and interval-set sections and records the limits: no optimal operation
ordering, automatic cell search, domain discovery or multivalued presence rule.

## Independent cover-pipeline consolidation (2026-11-06)

Based on #35 (`a72069e`), branch `test/finite-cover-integration`.

- `./check.sh` exited 0: Lake build, fresh standalone audit, and all 14 Python
  integration/enforcement tests (51.286 seconds). The semantic test runs two
  separately audited Lean fixtures in fresh processes. No warnings/errors in
  the final run, including fixture output checked by the runner.
- Core coverage remains 540 named checks, 1,025 imported namespace theorem/axiom
  declarations, and 54 registered/audit-reachable root modules. No root proof
  module, named audit, Lake target, dependency pin or axiom policy changed.
- The new tests/CoverPipeline.lean imports only core APIs and AuditPolicy. A new
  variable-valued conditional, restricted cell, output limit and reciprocal
  compose to exact coefficients [4/11,4/9]. The semantic contract proves endpoint
  existence and zero exclusion while preserving an interior coordinate-domain
  hole. The expression is separately shown defined at that excluded coordinate.
- Kernel controls distinguish global limit-one unknown, global limit-two success,
  restricted limit-one success and zero-capacity unknown. No milestone example
  theorem supplies the fixture's expected results or its input-domain proofs.
- The harness now requires every persistent Lean fixture to be registered and
  elaborated freshly with its own namespace audit. Compiler dependency closure
  checks reject transitive `*Examples` imports under the current naming convention.
  The eight existing forbidden-axiom/allowlist controls remain unchanged.
- GitHub metadata confirmed all 24 GIA PRs #11–#35 (excluding unrelated #31) open
  and unmerged, with exact predecessor head/base matches. Local first-parent
  ancestry from `158074a` to `a72069e` agrees. REVIEW_STACK.md records a dated table;
  earlier validation and historical guidance are preserved.
- `git diff --check` and the new fixture's placeholder/custom-axiom/native-shortcut
  scan passed. No new mathematical interface, app build/release change, hosted
  CI, FP complication, merge, base edit, rebase or force push. No blocker.

Final log: `/workspace/lean-tools/cover-integration-check.log`.
The focused fixture log was diagnostic: a rational-normalization proof issue
and subsequent linter warning were corrected before the successful full run.
A local `main` ref was absent; ancestry was checked against the verified main
commit SHA instead. Independence means a fresh client of the same core APIs and
Lean kernel, not an independent implementation or proof checker. The updated
assessment records remaining mathematical gaps and recommends review-first
consolidation rather than a broad interface refactor.

## Fuelled supplied-cell certification (2026-11-07)

Based on #36 (`b63f1da`), branch `feat/fuelled-cell-certificates`.

- `./check.sh` exited 0: full Lake build, standalone enforced audit, and all
  14 Python integration/enforcement tests (57.778 seconds), including three
  fresh-process semantic fixtures. No warnings/errors in the final run.
- Audit passed 546 named checks and 1,042 imported namespace theorem/axiom
  declarations. All 55 root modules are registered and audit-reachable. All six
  public core theorems have named audits. The new independent fixture separately
  passed its namespace audit (33 theorem/axiom declarations in the focused run).
  The allowlist and negative enforcement controls remain unchanged.
- The executable checker reuses evalGuarded once per attempted cell and reports
  an instrumented call counter. It is proved at most fuel for every verdict;
  certification checks exactly the list length. Exhaustion and an enclosure
  failure return unknown, with early failure stopping further attempts.
- A separate ParameterCover proof connects listed-cell success to defined Expr
  values at every enclosed coordinate point. Existing arithmetic continuity
  derives the whole-path certificate from continuous enclosed coordinates.
- The fresh fixture checks a rational expression whose whole-interval enclosure
  is unknown: two half-cell calls certify it, and the derived continuity plus
  endpoint signs yield an actual root. Fuel one is unknown despite that root.
- A shared-boundary pole stops after one attempt despite a larger budget. A
  gapped list passes its local checks but is proved not to cover the unit range;
  an empty list likewise cannot supply the coverage premise. Actual midpoint
  undefinedness is proved independently of the checker verdict.
- `git diff --check` and placeholder/custom-axiom/native-shortcut scans passed.
  No evaluator duplication/refactor, syntax, dependency pin, application/release,
  hosted CI or FP assumption changes. No merge or unresolved blocker.

Logs: `/workspace/lean-tools/cell-certification-core.log`,
`/workspace/lean-tools/cell-certification-fixture.log`, and
`/workspace/lean-tools/cell-certification-check.log`.
Initial projection/cast elaboration issues were corrected before the successful
focused and full runs. CELL_CERTIFICATION.md specifies the exact modeled unit:
top-level evaluator attempts, not time, memory, rational bit complexity, or
preemption inside a call. Coverage, coordinate enclosure/continuity, and any
external partial-environment membership remain explicit obligations.

## Automatic supplied-cell coverage checking (2026-11-07)

Based on #37 (`df385da`), branch `feat/checked-cell-coverage`.

- `./check.sh` exited 0: full build, standalone enforced audit, and all 14 Python
  integration/enforcement tests (54.166 seconds), including three fresh semantic
  fixtures. No warnings/errors in the final run.
- Audit passed 551 named checks and 1,049 imported namespace theorem/axiom
  declarations. All 56 root modules are registered and audit-reachable. All five
  public core theorems have named audits. The expanded CellCertificates fixture
  separately passed its namespace audit (62 declarations in the focused run).
  Axiom allowlisting and negative enforcement controls are unchanged.
- The executable rational endpoint scan is proved to imply ParameterCover. Its
  frontier uses max, so nested cells cannot move the covered endpoint backwards.
  Closed shared boundaries and overlapping chains are included.
- The combined checker validates geometry before calling the existing checkCells
  function. Successful definedness/continuity consumers no longer need a manual
  coverage proof. The same evaluator-attempt counter bound is preserved.
- The independent actual-root proof now uses the combined automatic path, while
  retaining the original supplied-coverage checks for comparison. Gapped and
  empty lists return unknown before evaluation; poles and fuel exhaustion retain
  the expected unknown reports.
- A valid reversed half-cell cover is proved to be a cover yet returns unknown,
  exposing deliberate order sensitivity. A nested-overlap chain is accepted and
  converted to a coverage proof. A redundant cell can still exhaust arithmetic
  fuel, since the entire supplied list is checked after geometric acceptance.
- `git diff --check` and placeholder/custom-axiom/native-shortcut scans passed.
  No evaluator/subdivision rewrite, FP assumptions, pins, application/release,
  hosted CI, merges or unresolved blockers.

Logs: `/workspace/lean-tools/cell-coverage-core.log`,
`/workspace/lean-tools/cell-coverage-fixture.log`, and
`/workspace/lean-tools/cell-coverage-check.log`.
The reversed-list membership proof was corrected before successful validation.
CELL_CERTIFICATION.md documents the new front end and retained limitations:
geometric comparisons are not metered by evaluator fuel; list recognition is
conservative and order-sensitive; coordinate continuity/enclosure and external
partial-environment membership are not automatically inferred.

## Adaptive cell certificates — 2026-11-07

Branch feat/adaptive-cell-certificates, based on #38 at 0a8582f. Pinned
Lean 4.19.0 and unchanged mathlib revision. `./check.sh` completed with exit 0:
full build, standalone enforced audit, 559 named audits, namespace scan of
1,071 theorem/axiom declarations, all 57 root modules registered and reachable,
and all 14 enforcement/integration tests passed (60.150s for the Python suite).
All three fresh semantic fixtures passed; CellCertificates independently
elaborated and audited 77 declarations using core imports only. The log is
/workspace/lean-tools/adaptive-cell-check.log. No warnings or errors appeared.

All eight new public core theorems have named allowlist audits; dependencies
remain restricted to propext, Classical.choice and Quot.sound. No placeholder,
custom axiom or native_decide occurs in the new core or updated fixture.
`git diff --check` passed. The initial targeted build exposed one missing natural
number inequality proof; adding omega resolved it before this full run.

Kernel-computed controls confirm a two-cell plan with three planning calls and
five total certification calls, retained unresolved leaves, separate depth/fuel
exhaustion, and early success without refinement. The actual-root proof now uses
generated cells. A semantic midpoint-hole theorem rules out pole certification
for every depth/fuel pair. No time/memory bound, completeness, FP implementation
correctness, external domain membership or conditional continuity is claimed.

## Finite-cover products — 2026-11-07

Branch feat/finite-cover-products, based on #39 at ddd65eb. Pinned Lean 4.19.0
and unchanged mathlib revision. Full `./check.sh` passed with exit 0: build,
standalone enforced audit, 563 named audits, 1,078 namespace theorem/axiom
declarations, all 58 root modules registered and reachable, and all 14
enforcement/integration tests (63.727s for the Python suite). All three fresh
semantic fixtures passed, including their namespace audits and core-only
dependency checks. Log: /workspace/lean-tools/cover-products-check.log.
No warnings or errors occurred in the final full run.

All four new core theorems have named audits with the unchanged allowlist
(propext, Classical.choice, Quot.sound). Source scans found no sorry, admit,
custom axiom or native_decide in the new core or changed fixture. The initial
fixture check exposed an extra tactic after a solved goal and an omitted
curvature unfolding; both were corrected before full validation. Its enforced
namespace audit rejected the incomplete proof via sorryAx during that check.

The independent client composes conditional interpretation, parameter restriction,
guarded reciprocal, multiplication and coalescing. It preserves the actual
midpoint hole, excludes zero and proves an actual product of one at an endpoint.
Multivalued controls compute four pairs, prove mixed products exist, reject a
zipped-pair enclosure, and distinguish independent choice from correlated square
semantics. `git diff --check` passed. No new FP assumptions, dependencies,
application/build/CI changes or merges.

## Shared-witness squares — 2026-11-07

Branch feat/shared-witness-squares, based on #40 at 3b21095. Pinned Lean 4.19.0
and unchanged mathlib revision. `./check.sh` exited 0: full build, standalone
enforced audit, 569 named checks, 1,085 namespace theorem/axiom declarations,
all 58 root modules covered, and all 14 enforcement/integration tests passed
(59.001s for the Python suite). All three fresh semantic fixtures passed with
namespace and core-only dependency checks. The expanded CoverPipeline fixture
also passed its focused audit of 71 declarations. Final log:
/workspace/lean-tools/shared-square-check.log. No warnings or errors.

All six added core theorems have named audits under the unchanged
propext/Classical.choice/Quot.sound allowlist. Source scans found no sorry,
admit, custom axiom or native_decide in the changed core/fixture. No new module,
evaluator, dependency or audit-policy change. `git diff --check` passed.

Checks include preserved partial-domain holes and endpoint existence through
conditional restriction, square and reciprocal; exact multivalued ±1 square
semantics; computed square bounds; rejection of square as an independent-product
replacement; and late-coalescing reciprocal success versus early-coalescing
unknown despite actual squares of one. No general witness-correlation inference,
optimal within-component square bounds, runtime/memory guarantee, FP assumption
change, application changes or merge is claimed.

## Threshold-local certificates — 2026-11-07

Branch feat/threshold-local-certificates, based on #41 at 316364c. Pinned
Lean 4.19.0 and unchanged mathlib revision. Full `./check.sh` exited 0: build,
standalone enforced audit, 573 named checks, 1,095 namespace theorem/axiom
declarations, all 59 root modules registered and reachable, and all 14
enforcement/integration tests (66.559s for the Python suite). Four registered
fresh semantic fixtures passed their namespace audits and core-only dependency
checks. Final log: /workspace/lean-tools/threshold-check.log. No warnings/errors.

All four public core theorems have named audits; private cell-transfer lemmas
are included transitively. The allowlist remains propext, Classical.choice and
Quot.sound. Source scans found no sorry, admit, custom axiom or native_decide in
the new core/fixture. The initial core needed an explicit ExpressionContinuity
import for value uniqueness; the result-equality fixture needed Option.some_get
rewrites instead of a nonexistent decidable equality for cover lists. These were
resolved before full validation. `git diff --check` passed.

Specification was checked against actual ConditionalValue constructors and the
existing local-parameter containment equivalence. Independent direct semantic
proofs accompany the new certificate clients for the discontinuous reciprocal
example. Controls cover global unknown/local success, zero exclusion despite
opposite endpoint signs, equality enclosed on the right, actual boundary-pole
undefinedness, conservative rejection of an inactive boundary pole, undefined
guards despite successful branch checks, degenerate endpoint cells, and a
counterexample to flattening local affine parameters.

No continuity, automatic guard identity, open-cell arithmetic, full domain
inference, external partial-environment membership, runtime bound or FP
implementation correctness is claimed. No application build/CI changes or merges.

## Finite-cover boundedness and inactive poles — 2026-11-07

Branch proof/finite-cover-boundedness, based on #42 at ed5a624. Pinned
Lean 4.19.0 and unchanged mathlib revision. Full `./check.sh` exited 0: rebuild,
standalone enforced audit, 576 named checks, 1,098 namespace theorem/axiom
declarations, all 59 root modules covered, and all 14 enforcement/integration
tests passed (68.966s for the Python suite), including four fresh core-only
semantic fixtures. The expanded ThresholdCertificates fixture also passed a
focused audit of 50 declarations. Final log:
/workspace/lean-tools/finite-bounds-check.log. No warnings/errors in the full run.

All three general boundedness theorems have named audits under the unchanged
propext/Classical.choice/Quot.sound allowlist. No new module, definition,
evaluator behavior, dependency or audit policy was introduced. Source scans
found no sorry, admit, custom axiom or native_decide in the changed core/fixture.
An initial removable-singularity proof needed an explicit div_self rewrite to
preserve its nonzero premise before simplification; the corrected fixture passed
both focused and full checks. `git diff --check` passed.

The independent fixture constructs actual values below every real lower bound
strictly inside the active branch and derives impossibility of any finite affine
cover globally and in the left cell's local parameter. It also constructs a
finite exact-one cover for a bounded removable-singularity example that the
current checker cannot certify. Actual Value.div witnesses retain explicit
nonzero proofs; no value is assigned to division by zero at the inactive boundary.
No FP assumptions, range-representation changes, application changes or merges.

## Executable domain queries (2026-11-07)

Based directly on main `8ce2199f6d2d72c0c47269d02b8e1f1aa8cde7f0`, without #44 or
#45 in this branch. Full `./check.sh` passed: Lean build, standalone enforced
axiom audit, 581 named checks, 1,103 imported namespace theorem/axiom declarations,
60 registered root modules, and all 14 Python enforcement/integration tests
across five fresh core-only semantic fixtures. The focused DomainQueries fixture
passed with 21 audited declarations and no warnings. Log:
`/workspace/lean-tools/domain-queries-check.log`.

An additional scratch copy of the fresh client evaluated the seven rational
queries with `#eval`, yielding `[no, yes, no, no, yes, yes, no]`, matching the
separate kernel-reduced theorem. This evaluation is not a proof shortcut.
Log: `/workspace/lean-tools/domain-query-compat/run.log`.

A separate, non-default compatibility check rebuilt `NonzeroDomains.lean` from
#45's exact head `9fb779e8843c317b30bdcca5097949c98083d43b` into
`/workspace/lean-tools/domain-query-compat/NonzeroDomains.olean`. With that path
prepended to `LEAN_PATH` inside `lake env`, `Compatibility.lean` elaborated and
audited two generic composition theorems: #45's quotient certificates supply
the new query wrappers' existence and exclusion premises. Both require supplied
membership decisions; neither requires finite quotient range bounds. This
one-off compatibility test does not import #45 into the committed build or
claim executable inference for its arbitrary real predicates. Source and log:
`/workspace/lean-tools/domain-query-compat/Compatibility.lean` and `check.log`.

All five public core theorems have named audits. Allowlist unchanged:
`propext`, `Classical.choice`, `Quot.sound`. No added placeholders, custom axioms,
or native proof shortcuts. `git diff --check` passed. No FP, app/release,
dependency, hosted CI, or merge changes.

## Automatic outer-quotient domains (2026-11-07)

Based on #46 head `5af426f12b2dd6686524479633a2bc178332125f`, with the unchanged
`NonzeroDomains.lean` prerequisite from #45 head
`9fb779e8843c317b30bdcca5097949c98083d43b`. Its blob hash was checked equal:
`030d95d3233f7bdb680612a2cad8c04c8c2f5274`. Neither PR was merged or modified.

Full `./check.sh` passed: Lean build, standalone enforced audit, 589 named
checks, 1,130 imported namespace theorem/axiom declarations, 62 root modules,
and all 14 Python enforcement/integration tests across six fresh core-only
semantic fixtures. Focused `tests/QuotientDomains.lean` passed with 44 audited
declarations. No warnings or errors in the completed full run. Log:
`/workspace/lean-tools/quotient-domains-check.log`.

The fixture proves exact inferred definite membership for the reciprocal at
all rational parameters and independently proves the same semantic definedness
set. It also covers an external hole, an actual pole, cancellation at zero,
collapsed zero denominator bounds, nested analysis failure with both actual
existence and absence, unsupported syntax, and loose crossing-zero bounds with
both defined/undefined concrete instances. A scratch `#eval` run produced the
same direct/nested/loose query results as the separately kernel-checked theorems:
`/workspace/lean-tools/quotient-domains/run.log`. No native proof shortcut is used.

All five new public core theorems and the three reused #45 theorems have named
audits. Unchanged `propext`, `Classical.choice`, `Quot.sound` allowlist; no added
placeholders or custom axioms. `git diff --check` passed. No FP assumptions,
application/release code, dependency pins, hosted CI, or merges changed.

## Recursive exact-point domain inference (2026-11-07)

Based on #47 head `00d1a4914e816da96ccee9449b05610602194556`. Full `./check.sh`
passed: Lean build, standalone enforced audit, 594 named checks, 1,137 imported
namespace theorem/axiom declarations, 63 root modules, and all 14 Python
enforcement/integration tests across seven fresh core-only semantic fixtures.
The focused PointDomains fixture passed with 34 audited declarations. No
warnings or errors occurred in the completed full run. Log:
`/workspace/lean-tools/point-domains-check.log`.

The new core proves successful evaluation supplies a value with a sound backend,
and proves completeness only for exact-backend rational singleton inputs. The
fresh fixture independently proves double-reciprocal partial semantics and its
exact inferred rational domain. Controls retain external holes and uncertainty,
strict zero-times-undefined and cancellation holes, the earlier interval
analyzer's unknown result, wide-interval failure despite a defined value, and a
sound declining backend failing even at singleton inputs. A scratch `#eval` run
matched the separate kernel-reduced query proofs:
`/workspace/lean-tools/point-domains/run.log`.

All five new public core theorems have named audits. Unchanged allowlist:
`propext`, `Classical.choice`, `Quot.sound`; no placeholders, custom axioms or
native proof shortcuts. `git diff --check` passed. No new evaluator, FP
assumptions, dependency pins, application/release changes, hosted CI or merges.

## Uncertain-input recursive-domain feasibility (2026-11-07)

Based on #48 head `404271d5b6e19c2df89825e4446afb5671c28548`. No production Lean
module or public mathematical API changes. The new fresh core-only fixture
`tests/UncertainDomains.lean` elaborated and passed its namespace audit of 28
declarations without warnings. Full `./check.sh` passed: build, standalone
enforced audit, unchanged 594 named checks and 1,137 imported namespace
theorem/axiom declarations, 63 root modules, and all 14 Python tests in 79.122s
across eight fresh semantic fixtures. Log:
`/workspace/lean-tools/uncertain-domain-feasibility-check.log`.

The fixture proves exact projected child-value relations with sound partial
enclosures, valid independent-witness addition, absence of a shared-input sum,
and the impossibility of reinterpreting the independent enclosure as an AST
certificate. A positive uniform-child composition theorem states sufficient
conditions. Midpoint and external-hole controls rule out an unsupported witness.
An explicit unbounded uncertain-input reciprocal relation is shown not to admit
any finite affine cover using the existing boundedness theorem. Current guarded
analysis remains unknown, verified by kernel reduction.

The unchanged allowlist is `propext`, `Classical.choice`, `Quot.sound`. No new
axioms, placeholders, native proof shortcuts, FP assumptions, dependencies,
application/release changes, hosted CI or merges. `git diff --check` passed.

## Shared-environment optional-range prototype (2026-11-07)

Based on #49 head `a68996dfac7b4036d674e9d4327039221199e76f`. The representation
experiment is confined to `tests/OptionalRangePrototype.lean`; no production
module imports it. Focused elaboration passed with 23 audited declarations.
Full `./check.sh` passed: build, standalone enforced audit, unchanged 594 named
checks and 1,137 imported namespace theorem/axiom declarations, 63 root modules,
and all 14 Python tests in 86.330s across nine fresh core-only fixtures. No
warnings/errors. Log: `/workspace/lean-tools/optional-range-prototype-check.log`.

Proofs cover faithful embedding of the existing contract, sound range forgetting,
addition with known or unavailable ranges, exact shared-environment expression
composition, reciprocal partial-semantic equivalence, known existence without a
range, exclusion at a pole, disjoint child domains, and inconclusive domains
supporting both empty and nonempty relations. This is semantic validation, not
an executable constraint solver or production API adoption.

Unchanged `propext`, `Classical.choice`, `Quot.sound` allowlist. No placeholders,
custom axioms, native proof shortcuts, FP assumptions, dependency pins,
application/release changes, hosted CI or merges. `git diff --check` passed.

## Shared-environment affine domain guards (2026-11-07)

Based on #50 head `ee23e8e49965bd474237806f55a9327467ed9de0`, verified still open
and unchanged before publication. Full `./check.sh` passed: Lean build,
standalone enforced audit, 602 named checks, 1,159 imported namespace
theorem/axiom declarations, 64 root modules, and all 14 Python tests in 92.811s
across ten fresh core-only fixtures. Focused AffineDomainGuards fixture: 25
audited declarations. No warnings/errors in the completed run. Log:
`/workspace/lean-tools/affine-domain-guards-check.log`.

The core proves exact definedness for the generated reciprocal-sum family over
all real shared environments, append/conjunction correspondence, rational/real
guard equivalence and both external-domain semantic directions. Independent
controls revisit disjoint witnesses and an excluded valid midpoint, establish
a two-coordinate real domain and a concrete Value, exercise both query wrappers,
and check uncertainty, empty/duplicate lists and a zero denominator. Separate
`#eval` runs matched the kernel-reduced query proofs:
`/workspace/lean-tools/affine-domain-guards/run.log`.

All eight new public core theorems have named audits. Unchanged allowlist:
`propext`, `Classical.choice`, `Quot.sound`. No placeholders, custom axioms or
native proof shortcuts. `git diff --check` passed. No existing API migration,
range assertions, FP assumptions, dependency pins, application/release changes,
hosted CI or merges.

## Affine segment-domain integration (2026-11-07)

Branch `feat/affine-segment-domains`, based on #51 at
`c385d0e08284c82429eca53beedde64edd2efdaf`. Pinned Lean 4.19.0 and mathlib
`c44e0c8ee63ca166450922a373c7409c5d26b00b` unchanged.

- Focused `lake build AffineSegmentDomains` and fresh
  `lake env lean tests/AffineSegmentDomains.lean` passed; 25 fixture declarations
  passed its namespace audit.
- `./check.sh` exited 0: full build, standalone audit, 607 named checks,
  1,164 namespace theorem/axiom declarations, 65 registered root modules,
  and 14 Python tests in 91.848 seconds. All 11 independent semantic fixtures
  ran in fresh processes. Negative controls reject sorry/custom axioms and
  missing audit coverage. No warnings or errors in the completed log.
- Log: `/workspace/lean-tools/affine-segment-domains-check.log`.
- Separate runtime evaluation in `/workspace/lean-tools/affine-segment-run.lean`
  returned `(unknown, present, unknown)` for the old safe-path example, the new
  domain-aware certificate, and a sign change across a pole respectively.
- All five public theorems are named in Audit.lean. The axiom allowlist remains
  `propext`, `Classical.choice`, `Quot.sound`; no new axioms or native proof shortcuts.
- 55 local Markdown file/heading links in the four edited guides checked,
  with no failures. `git diff --check` passed.

Controls include an independently constructed actual root, an actual off-path
pole, a reciprocal that changes sign but has no zero, endpoint poles, rejected
out-of-box endpoints, backend failure, and an external restriction that removes
zeros. The checker does not claim presence inside arbitrary external domains.
README now supplies navigation, conceptual reading order, and an explicit
merged/under-review distinction. Historical receipts were preserved. No app,
release, CI, FP assumption, dependency pin or existing API changes; no merges.

## Thesis concordance documentation (2026-11-07)

Branch `docs/thesis-concordance`, based on #52 at
`9efa154bd09e8a9a2198974da6aaf1e37102746c`. Documentation only; the preceding
milestone's mathematical sources and pinned dependencies are unchanged.

The author's HTML contents and the specifically linked source sections were
read against the current Lean declarations. The PDF text extraction was garbled;
this limitation is recorded in the concordance, with no invented theorem-number
or full-formula correspondence. Local validation checked 104 file/heading links
in README and THESIS_CONCORDANCE with no failures. A generated scratch Lean file
imported the built Audit environment and resolved all 38 cited snake-case
project theorem names with `#check`; it exited 0. Logs:
`/workspace/lean-tools/concordance-declarations.lean` and
`/workspace/lean-tools/concordance-declarations.log`.

The existing full Lean build/audit was not rerun for unchanged proofs; see the
preceding exact validation receipt. `git diff --check` passed. No API, FP
assumption, application, dependency, CI or merge changes. README preserves the
same front door and now acknowledges the singleton completeness exception.

Follow-up within the concordance milestone: added a chapter-ordered roadmap
comparing current hypotheses/conclusions, reusable dependencies, and missing
source-comparison obligations. Rechecked the same 104 local links and the
expanded 41 theorem references; the scratch Lean check again exited 0. Exact
formula comparison remains blocked: web GIF retrieval is unsupported, Chromium
reported DNS failure, and the inherited-proxy request to
`https://www.dgp.toronto.edu/~mooncake/thesis/img408.gif` returned CONNECT HTTP 403.
No image was downloaded, no denied operation retried, and no proof-equivalence
claim or mathematical change was introduced to work around that limitation.

PDF screenshot follow-up (2026-11-07): the authorized web tool opened the official
PDF as 173 pages. Screenshot calls using the returned PDF reference for zero-based
pages 0 and 80 succeeded at the tool layer, but this execution wrapper returned
only a 223-character citation string, without any image content/bytes. No visual
formula inspection was possible from that response. The current concordance now
distinguishes this delivery limitation from source availability. No denied GIF
request was retried, no source equivalence upgraded, and no Lean source changed.

## Restricted segment-domain completeness (2026-11-07)

Branch `feat/affine-segment-domain-completeness`, based on #53 at
`ba976a57f4060352efa1c1d0f283e2e8438e186e`. Pinned toolchain and dependencies
unchanged. Focused `lake build AffineSegmentDomains` and the fresh
`tests/AffineSegmentDomains.lean` check passed; its namespace audit now covers
35 declarations, including generated proof auxiliaries.

`./check.sh` exited 0: full build, standalone audit with 609 named checks and
1,169 namespace declarations, and all 14 Python tests in 120.036 seconds.
All 11 semantic fixtures ran freshly; the same 65 root modules are registered.
Completed log: `/workspace/lean-tools/affine-segment-completeness-check.log`.
No warnings or errors. Both new public theorems have named audits, including
transitive dependencies on the private intermediate-value helper. The existing
`propext`, `Classical.choice`, `Quot.sound` allowlist is unchanged.

New controls cover an actual hole derived from the converse, valid and invalid
degenerate segments, the empty guard family, a segment with both a hole and an
actual zero, and a safe segment whose numerical presence check remains unknown.
110 local links/headings in edited guides passed; `git diff --check` passed.
No executable definition, existing API contract, FP assumption, app/release,
dependency or CI changes, and no merges. This is an independently specified
project result; no uninspected thesis equation correspondence is claimed.
No denied PDF/GIF access was retried during this milestone.

## External-domain presence bridge (2026-11-07)

Branch `feat/affine-presence-domain-bridge`, based on #54 at
`8739adff1b4fd8169c03cc1634017d3fee88555c`. Pinned Lean/mathlib unchanged.
Focused module build and the fresh AffineSegmentDomains fixture passed; the
fixture namespace now audits 50 declarations, including generated auxiliaries.

`./check.sh` exited 0: full build, standalone audit with 613 named checks and
1,173 namespace declarations, and 14 Python tests in 95.097 seconds. All 11
semantic fixtures ran freshly; the same 65 root modules are registered. No
warnings or errors. Log:
`/workspace/lean-tools/affine-presence-domain-bridge-check.log`.
The four added public theorems have named audits; the prior presence theorem
retains its statement and named audit. The axiom allowlist is unchanged.

Positive controls establish quadrant path inclusion, restricted definedness and
an actual restricted root. Negative controls prove that a domain admitting both
endpoints can exclude all zeros and fail whole-path inclusion. Restricted absence
is checked for an arbitrary predicate. 112 local file/heading links in README,
THESIS_CONCORDANCE, GENERALIZED_INTERVALS and REVIEW_STACK passed, as did
`git diff --check`. No executable definitions, previous theorem contracts, FP
assumptions, app/release, dependency or hosted CI changes; no merges. Denied
source downloads were not retried and exact-thesis caveats remain in force.

## Constructive affine external-region checks (2026-11-07)

Branch `feat/affine-external-domain-checks`, based on #55 at
`e7c60ee7fd295ebe4630ff44bee400b0edced30a`. Pinned dependencies unchanged.
Focused module build and fresh AffineRegions fixture passed; its namespace audit
covers 35 declarations, including generated auxiliaries.

`./check.sh` exited 0: full build, standalone audit with 618 named checks and
1,183 namespace declarations, and all 14 Python tests in 109.621 seconds. The
66 root modules and 12 fresh semantic fixtures pass integration coverage.
No warnings or errors. Log: `/workspace/lean-tools/affine-regions-check.log`.
Five public theorems have named transitive audits; axiom allowlist unchanged.

Controls include a computed region certificate feeding actual root existence,
independent interpretation of the constraints, closed boundary contact, mixed
membership, uniform exclusion, degenerate paths, empty/zero constraints,
an inconsistent conjunction conservatively returning unknown, and an excluded
path coexisting with a genuine root elsewhere in the same box. Additional
external holes cannot be inferred from the constraint list.

Separate runtime evaluation matched the kernel proofs with
`(yes, no, unknown, unknown)`; files:
`/workspace/lean-tools/affine-regions-run.lean` and
`/workspace/lean-tools/affine-regions-run.log`. 117 local links/headings across
five updated guides passed; `git diff --check` passed. No prior API migration,
FP assumptions, app/release, dependency or hosted CI changes; no merges or denied
source-access retries. This is a restricted project integration, not a claimed
exact formalization of an uninspected thesis formula.

## Finite affine-region segment search (2026-11-07)

Branch `feat/affine-region-segment-search`, based on #56 at
`ad579edf1a378a6dde1264770cca6f1373ba99cc`. Dependencies unchanged. Focused
AffineRegionSearch build and its independent fresh fixture passed; the fixture
audits 34 declarations including generated auxiliaries.

`./check.sh` exited 0: full build, standalone audit with 625 named checks and
1,194 namespace declarations, and 14 Python tests in 102.692 seconds. All 67
root modules and 13 fresh semantic fixtures pass integration coverage. No
warnings or errors. Log: `/workspace/lean-tools/affine-region-search-check.log`.
Seven public theorems have named audits; the axiom allowlist is unchanged.

Independent controls include automatic restricted presence, first-match
membership, reverse sign orientation, directly constructed real roots, an
incomplete automatic policy recovered by a supplied candidate, empty search,
backend failure, an inadmissible center for a pole-free constant expression,
path exclusion that cannot justify box absence, and genuine arithmetic emptiness.
Separate runtime checks returned `(present, unknown, present, empty)` as proved;
see `/workspace/lean-tools/affine-region-search-run.lean` and its `.log`.
118 local links/headings across the five updated guides passed after the README
entry-point update. `git diff --check` passed.

The candidate type, eight-segment policy, List.find? implementation and ResultSound
contract are reused. No previous API migration, new FP assumptions, app/release,
dependency or CI changes, merges, or denied-source retries. Exact-thesis caveats
remain explicit; finite certificate completeness is not root-search completeness.

## Affine-region bounded subdivision (2026-11-07)

Branch `feat/affine-region-subdivision`, based on #57 at
`7b375e95ab5ff311f2c87759d78e9ac79b33194e`. Pinned dependencies unchanged.
Focused AffineRegionSubdivision build and fresh fixture passed; the fixture
audits 29 declarations including generated auxiliaries.

`./check.sh` exited 0: full build, standalone audit with 632 named checks and
1,201 namespace declarations, and 14 Python tests in 112.035 seconds. All 68
root modules and 14 fresh semantic fixtures pass integration coverage, including
the prior ordinary subdivision examples. No warnings or errors. Log:
`/workspace/lean-tools/affine-region-subdivision-check.log`. Seven new public
theorems have named audits. The unchanged allowlist is `propext`,
`Classical.choice`, and `Quot.sound`; rejection controls for sorry/custom axioms
pass. 119 local links/headings across the five updated guides and
`git diff --check` pass.

Kernel-computed controls prove depth zero/one unknown and depth two present for
`1/x + 1/y` on the wide box restricted by `x ≤ -1` and `y ≥ 1`. A separate proof
constructs the actual root `(-1,1)` without classifier soundness. Other controls
cover declined backends, an infeasible region that stays unknown, arithmetic
absence, shared-boundary roots, and degenerate boxes with/without a pole.

The shared refinement engine preserves the original ordinary subdivision API
and zero/successor equations. Exact constrained split equivalences retain the
same external region in both closed children. No additional FP assumptions,
app/release/dependency/CI changes, merges or denied-source retries. Depth is not
a work/time bound; no convergence or exact-thesis correspondence is claimed.

## Domain/search cross-milestone consolidation (2026-11-07)

Branch `test/domain-search-integration`, based on #58 at
`7ea8ab5ad52f84209159f461cccb057a5f230b5c`. No production Lean module, API,
backend, dependency, or axiom policy changed. The fresh integration fixture passed
its focused kernel check and namespace audit (20 declarations including auxiliaries).

`./check.sh` exited 0: full build, standalone audit (632 named checks and 1,201
namespace declarations), and 14 Python tests in 116.628 seconds. All 68 root
modules and 15 fresh semantic fixtures pass coverage checks. No warnings/errors.
Log: `/workspace/lean-tools/domain-search-integration-check.log`. The audit
rejection controls pass unchanged. 67 local documentation links/headings and
`git diff --check` passed.

The fixture proves agreement of singleton success and affine guards for arbitrary
generated reciprocal sums. An independent exact zero-set proof for `1/x + 1/y`
supports point/pole/range/search controls and a stricter external-domain
counterexample. Domain certainty does not imply a zero; a missing interval range
does not imply undefinedness; presence for one region cannot ignore extra holes.

GitHub metadata for #44–#58 was inspected: all open/unmerged at the heads recorded
in REVIEW_STACK; #46–#58 predecessor bases matched exactly. The NonzeroDomains
core was checked byte-identical against #45. This does not validate a combined
#44/#45 integration tree. Historical snapshots are preserved and labelled.
No merge, rebase, retarget, hosted CI, FP change or denied-source retry occurred.

## Independent-branch integration preparation (2026-11-07)

Branch `docs/lean-merge-plan`, based on #59 at
`050ffd22c9ae0e4374045bbf599514966516c6d1`. Documentation only; no production or
fixture source changes. GitHub metadata rechecked #44–#59 as open/unmerged at
the full heads listed in MERGE_PLAN. Chain predecessor bases match exactly.

Tree-only `git merge-tree --write-tree` analysis returned exit 1 with content
conflicts: #45/#59 in eight files, #44/#59 in five files, #44/#45 in five files.
The files and safe-resolution obligations are recorded in MERGE_PLAN. This
writes unreferenced Git tree objects, not merge commits or refs; the index and
worktree were unchanged by the analysis. Scratch outputs:
`/workspace/lean-tools/merge-review/{45-with-59,44-with-59,44-with-45}.txt`.

Original source bytes were extracted with `git show` into that scratch directory.
#45's NonzeroDomains fixture passed against #59 libraries (19 audited
declarations). #44's GuardedSimplification compiled with Lean 4.19.0 using an
isolated import overlay; its original ThresholdCertificates fixture passed
(70 audited declarations), as did its three public theorem audits. Only the
existing axiom allowlist occurred. Guarded check log:
`/workspace/lean-tools/merge-review/guarded-check.log`. No warnings/errors.

These targeted compatibility checks supplement #59's full validation; they do
not constitute a fully resolved combined-tree build. The plan explicitly requires
that build and registration/link checks after actual conflict resolution.
68 local links/headings and `git diff --check` passed for this documentation
increment. No merge, rebase, retarget, hosted CI, FP change or source-access retry.

## Repository-source concordance update (2026-11-07)

Branch `docs/thesis-paper-source-map`, based on #60 at
`7c1997d5b785bf7b5cf9d3063b9a0cabb4706cc1`. Documentation only. The graphing
repository's existing technique inventory and September 23 source-led review
provide the navigation baseline; this is not a replacement inventory.

Sources are pinned to graphing commit
`18f2e0e22a4a5a7893a87252bd0722c919d9a546`. Selected original PDF pages were
rendered and visually inspected: thesis PDF pp.7–8, 36, 40, 43–46, 50–53;
paper PDF pp.1, 6–7. The updated concordance records the scope, exact page
references, Markdown transcription differences, and separate paper track.
The paper renderer emitted ICC profile warnings but the pages were readable.
No blanket transcription certification is claimed.

The GitHub text connector could not deliver the binary PDF. An ordinary clone
of the separately authorized graphing repository supplied both PDFs successfully.
No denied website request was retried or bypassed. The existing source-access
history is retained, with the repository-copy availability update stated separately.

The local combined integration rehearsal remains frozen at tree
`d12791efa919085a5540d604c68a44754047807a`; it is not included in this branch.
Its full validation and source-union review are in
`/workspace/lean-tools/merge-review/REHEARSAL_RESULT.md`. This documentation
update neither merges #44/#45 nor claims their ancestry has been integrated.
The #60 introduction now correctly distinguishes #47–#59 predecessor matches
from #46 targeting main.

58 local links/headings in the changed concordance and plan passed, as did
`git diff --check`. No Lean source, FP contract, dependency or CI changes;
no repeat Lean build was needed for this documentation-only update.

## Finite-rational affine source correspondence (2026-11-07)

Branch `proof/affine-coefficient-correspondence`, based on #61 at
`be6fc0b2f4b438aa391597f5585bc77b1a0b6e6d`. Source navigation starts with graphing
inventory F06 and its source-review ledger, pinned to graphing commit
`18f2e0e22a4a5a7893a87252bd0722c919d9a546`. The original thesis §2.9.3,
printed pp.28–29/PDF pp.44–45, was visually checked in the preceding source
review; this increment matches its coefficient semantics and non-collapsing
condition only for finite rational coefficients.

Focused LinearIntervals/LinearEvaluator builds and the fresh AffineCorrespondence
fixture passed (21 audited declarations including generated auxiliaries).
`./check.sh` exited 0: full build, standalone audit with 639 named checks and
1,210 namespace declarations, and 14 Python tests in 127.058 seconds. All 68
root modules and 16 fresh semantic fixtures pass integration coverage. No
warnings/errors. Log: `/workspace/lean-tools/affine-correspondence-check.log`.
Seven added public theorems have named audits. The allowlist remains `propext`,
`Classical.choice`, `Quot.sound`; rejection controls pass. 126 local links/headings
in the four updated guides and `git diff --check` passed.

The fixture checks negative slopes, representation existence and failure,
nonlinear/out-of-domain counterexamples, evaluator-driven source cancellation,
its exact zero set, ordinary [-1,1] subtraction and a nonconstant band. Existing
proofs are reused, and no new root module, interval structure or evaluator is
introduced. Conversion functions have both round trips, value equality,
containment translation and necessary/sufficient ordering proofs.

No extended-real coefficient, optimal demotion, source-wide equivalence or IEEE
implementation claim is made. No FP assumptions, dependency/CI/app changes,
merges or denied-source retries. The earlier combined #44/#45 rehearsal remains
separate and has not been rebuilt to include this later milestone.

## Constant-interval source embedding (2026-11-07)

Branch `proof/constant-interval-embedding`, based on #62 at
`3b317c38df9cbeb482df7e18db3670bd23f01898`. Source navigation uses graphing
inventory F06 and its source-review ledger at commit
`18f2e0e22a4a5a7893a87252bd0722c919d9a546`. Thesis §2.9.4,
printed p.30/PDF p.46, supplies the zero-slope injection and an interval-extension
homomorphism claim. This increment proves the finite-rational injection and
preservation of the existing concrete addition, subtraction and multiplication
operations; it does not formalize the source's general operator construction.

Focused builds and the fresh ConstantEmbedding fixture passed (22 audited
declarations). `./check.sh` exited 0: full build, standalone audit with 646 named
checks and 1,217 namespace declarations, and 14 Python tests in 173.048 seconds.
All 68 root modules and 17 fresh semantic fixtures pass integration coverage.
No warnings/errors. Log: `/workspace/lean-tools/constant-embedding-check.log`.
Seven new public theorems have named audits; the axiom allowlist remains
`propext`, `Classical.choice`, `Quot.sound`, with rejection controls passing.
132 local links/headings in the four updated guides and `git diff --check`
passed.

The fixture checks the nested polynomial (x+y)*(x-y), its exact computed
interval [-42,28], an actual value and enclosure, and distinct constant images.
Controls retain ordinary dependency loss, demonstrate that the hull does not
commute with multiplication on arbitrary linear intervals, and show why the
interpreter correspondence is conditioned on successful linear interpretation:
ordinary guarded division can succeed where the polynomial interpreter returns
unknown. No replacement evaluator or root module is introduced.

No extended-real coefficients, optimal interval-extension correspondence, FP
implementation correctness, new FP assumptions, dependency/CI/app changes or
merges. The earlier combined #44/#45 rehearsal remains separate and has not
been rebuilt to include this later milestone.

## Quadratic fixed-chord corrections (2026-11-07)

Branch `proof/quadratic-chord-corrections`, based on #63 at
`4845d6bd2f2d53ea1fa44ed65b9500c456c54d70`. Consulted graphing inventory F07
and source-review records at `18f2e0e22a4a5a7893a87252bd0722c919d9a546`, then
visually checked thesis §2.9.5 on printed p.30/PDF p.46 and SIGGRAPH §5 on PDF
p.3. The thesis introduces extended-real quadratic coefficients and defers
demotion. The paper passage specifies ordinary interval arithmetic. These
finite-real sharp-correction theorems are a derived representation bridge,
not a claimed transcription of a source theorem or later demotion algorithm.

Focused LinearMultiplication/LinearEvaluator builds and the QuadraticChord
fixture passed (11 audited declarations). The initial concave-example proof
needed algebraic normalization; the enforced audit rejected its unfinished
proof before correction. The final full `./check.sh` exited 0: build, standalone
650 named audits and 1,221 namespace declarations, and all 14 Python tests in
138.732 seconds. Integration covers 68 root modules and 18 fresh fixtures.
No warnings/errors in the final Lean check log:
`/workspace/lean-tools/quadratic-chord-check.log`.
All four new public theorems have named audits. The unchanged allowlist is
`propext`, `Classical.choice`, `Quot.sound`; rejection controls pass.
137 local links/headings across four updated guides and `git diff --check`
passed.

Controls cover positive, negative and zero curvature, insufficient correction,
extrapolation outside the unit interval, and incomparable affine lower bounds.
An interpreter-driven square example has a separate Value witness, semantic
enclosure proof, and equality at the sharp lower bound's midpoint. General
coefficients are real; the affine-product representation uses rational inputs.
The two iff theorems prove optimality only among vertical shifts of the same
endpoint chord. No new root module, evaluator, partial-domain behavior or FP
assumption. No dependency/app/CI changes or merges. The separate combined-tree
rehearsal remains untouched and does not include this milestone.

## Two-parameter affine non-collapse (2026-11-07)

Branch `proof/two-parameter-affine-order`, based on #64 at
`d8b7352aa8bc7e203e1142a4719c3f259ed346de`. Source navigation used graphing
inventory F06/F07 and the existing source-review ledger at
`18f2e0e22a4a5a7893a87252bd0722c919d9a546`. Original thesis §§2.9.6–2.9.7,
printed pp.30–31/PDF pp.46–47, establish independent parameters and pointwise
non-collapse. The finite four-corner criterion is derived here, rather than
attributed to a separately stated source theorem. Scope is two independent
parameters and finite rational coefficient forms; the supporting real affine
lemma permits arbitrary real coefficients.

Focused AffineDomainGuards build and the TwoParameterBounds fixture passed
(16 audited declarations including generated auxiliaries). Full `./check.sh`
exited 0: build, standalone audit with 654 named checks and 1,226 namespace
declarations, and 14 Python tests in 174.770 seconds. All 68 root modules and
19 fresh semantic fixtures pass coverage. No warnings/errors in the final log:
`/workspace/lean-tools/two-parameter-check.log`.
Four new public theorems have named audits; the axiom allowlist remains
`propext`, `Classical.choice`, `Quot.sound`, with rejection controls passing.
143 local links/headings in four updated guides and `git diff --check` passed.

The positive fixture uses mixed-sign coefficients and connects a computed
acceptance to actual expression Value semantics at arbitrary square points.
Counterexamples cover diagonal-only checking, omission of the fourth corner,
nonlinear functions, extrapolation and interpreting a false result as absence.
The test is equivalent to nonempty fibers of existing FunctionalBounds
throughout the square; no replacement representation/evaluator is added.

No extended-real coefficient validity, arbitrary-dimensional algorithm,
nonlinear criterion, FP behavior or paper branch-choice semantics is claimed.
No FP assumptions, partial-domain behavior, dependencies, app build or hosted
CI changed. No merges or denied-source retries. The earlier combined-tree
rehearsal remains untouched and excludes this later milestone.

## Universal input-domain semantics milestone (2026-11-07)

Branch `proof/universal-input-domains`, based on #65 at
`e2c806c09b043cda292c1b176cfe0db35bacf902`. Source navigation used graphing
inventory F08/F15 and its source-review ledger at
`18f2e0e22a4a5a7893a87252bd0722c919d9a546`. Visually rechecked thesis
§§2.11.1–2.11.2, printed pp.34–35/PDF pp.50–51, and SIGGRAPH §8/PDF p.4.
The PDF's three-valued equivalence overrides the damaged Markdown implication.
The layer interprets domain compatibility propositionally, preserves every
admitted input witness, and relates logical Boolean extrema to domain precision
on nonempty fibers. It does not formalize the full truth algebra or λ arithmetic.

Focused UniversalDomains build and fixture passed (27 audited declarations).
Initial fixture elaboration issues were corrected; unfinished proofs were
rejected by the enforced audit. Final `./check.sh` exited 0: full build,
standalone audit with 663 named checks and 1,237 namespace declarations, and all
14 Python tests in 143.043 seconds. Integration coverage includes 69 root
modules and 20 fresh semantic fixtures. No warnings/errors in the final log:
`/workspace/lean-tools/universal-domains-check.log`.
All nine public theorems have named audits. The allowlist remains `propext`,
`Classical.choice`, `Quot.sound`; rejection controls pass. 150 local links/headings
in the four updated guides and `git diff --check` passed.

The fixture proves actual partial reciprocal behavior at inputs 0 and 1,
exhibits a valid existential contract that fails universal definedness, and
corrects it with an uncertain exact envelope. It tests same-input addition,
vacuous empty fibers, and incompatible separately chosen input witnesses.
A guarded reciprocal example certifies all admitted x in [1,2], preserves an
external hole, and projects only after proving input nonemptiness. No numerical
value from totalized division is accepted without a Value proof.

One new root module groups compatibility, universal soundness, projection,
logical exact envelope/precision, same-input composition, restriction, and
existing guarded evaluator integration. Existing APIs are preserved. The
admitted-input and relation interpretations remain explicit caller obligations.
The exact envelope is logical, not an executable inference procedure; its
empty-fiber convention is not asserted equivalent to the source's convention.
Symbolic intervals, floating conversion, extended-real values, domain demotions
and the full property calculus remain documented gaps. No FP assumption,
application, dependency-version or hosted-CI changes; no merges. The separate
combined-tree rehearsal remains untouched and excludes this later milestone.

## Partial square-root domain model (2026-11-07)

Branch `proof/square-root-domain-model`, based on #66 at
`35eec824008be8f9bd9510431f74f4c94b1a0bf2`. Source navigation used graphing
inventory F08/F15 and its source-review ledger at
`18f2e0e22a4a5a7893a87252bd0722c919d9a546`. Original thesis §2.11.5,
printed p.36/PDF p.52, and SIGGRAPH §8/PDF p.4 were checked visually. The paper
supplies the precise three branches; exact Real.sqrt replaces rounded endpoint
operations. The apparent [-1,-1] typo in the thesis's final decorated example
and the different absent payload conventions are recorded, not silently equated.

Focused SquareRootDomains build and fixture passed (16 audited declarations).
The new mathlib sqrt import required building additional components of the
existing pinned dependency. An initial fixture invocation preceded its completed
build; after that, two fixture lemma-name/normalization issues were corrected.
Final `./check.sh` exited 0: full build, standalone audit with 669 named checks
and 1,245 namespace declarations, and all 14 Python tests in 149.265 seconds.
Coverage includes 70 root modules and 21 fresh semantic fixtures. No
warnings/errors in the final log `/workspace/lean-tools/square-root-check.log`.
Six public theorems have named audits; the unchanged axiom allowlist is
`propext`, `Classical.choice`, `Quot.sound`, with rejection controls passing.
156 local links/headings in four updated guides and `git diff --check` passed.

The independent fixture checks negative/mixed/nonnegative ranges and the zero
boundary, rejects totalized negative square root as a partial value, and shows
why loose bounds can remain uncertain for actually defined inputs. It composes
nested roots and same-input addition, preserves an external hole, and connects
to the existing guarded evaluator with its enclosure/definedness hypotheses.

The model is noncomputable exact-real arithmetic. There is no new Expr syntax,
rational sqrt algorithm, directed-rounding assumption or IEEE implementation
claim. Nonnegative branch equivalence states endpoint ordering explicitly;
negative payloads are irrelevant because no result is possible. No dependency
version, app build or hosted-CI change; no merges. The separate combined-tree
rehearsal remains untouched and excludes this milestone.


### Square-root source wording correction (2026-11-07)

Independent review corrected the preceding receipt's interpretation of the
printed [-1,-1] example. Its uncertain domain permits undefinedness, and the
numeric enclosure is vacuous without any value. It is loose but sound, not a
false assertion. A typo remains plausible but unestablished. Current guides and
PR wording now distinguish this from the paper algorithm's precise absent
classification. No Lean source or hypotheses changed; the preceding full check
remains applicable. Local links/headings and diff checks were repeated.

## Property-composition source obstruction (2026-11-07)

Branch `test/property-composition-source-review`, based on corrected #67 at
`59d376a668e142b69051ab6cd46bfbff9b30df94`. Source navigation used inventory
F09 and the source-review ledger at graphing commit
`18f2e0e22a4a5a7893a87252bd0722c919d9a546`. Checked the original thesis
§2.12 on printed pp.36–37/PDF pp.52–53 and SIGGRAPH §10/PDF p.5. The literal
unary specialization of the printed weak-checkability direction is obstructed
by a constant outer function and a discontinuous total real child. The valid
sufficient direction is proved independently; no intended correction is assumed.

The fresh PropertyComposition fixture passed (8 audited declarations including
auxiliaries). An initial composition-lemma invocation was corrected before
validation. Full `./check.sh` exited 0: build, standalone 669 named checks and
1,245 namespace declarations, and 14 Python tests in 154.167 seconds. Coverage
includes 70 root modules and 22 fresh semantic fixtures. No warnings/errors in
the final log `/workspace/lean-tools/property-composition-check.log`.
The existing allowlist and rejection controls pass; fixture namespace auditing
covers every new theorem. 160 local links/headings in four updated guides and
`git diff --check` passed.

The test derives discontinuity from the existing intermediate-value theorem,
then proves existence of a point where the composite check holds and recursive
child check fails. Only ordinary total real functions and a true leaf flag are
used. This is distinct from the earlier square-root wording issue: that loose
interval result remains sound under uncertain definedness. #67's current docs
and PR body were corrected separately; its proofs were unchanged.

No production Lean API, FP assumptions, dependencies, app or CI changes. A
generic property framework remains deferred pending a decision on the intended
specification or additional source hypotheses. Existing specific continuity
proofs remain valid. No merges; the separate combined-tree rehearsal is intact.


<!-- Historical material from PR #44; original milestone claims and validation follow unchanged. -->

## Guarded threshold cancellation — 2026-11-07

Branch feat/guarded-threshold-cancellation, based on #43 at a3500ad. Pinned
Lean 4.19.0 and unchanged mathlib revision. Full `./check.sh` exited 0: build,
standalone enforced audit, 579 named checks, 1,101 namespace theorem/axiom
declarations, all 60 root modules covered, and all 14 enforcement/integration
tests passed (77.995s for the Python suite), including four fresh semantic
fixtures. The expanded ThresholdCertificates fixture also passed a focused
namespace audit of 70 declarations. Final log:
/workspace/lean-tools/guarded-cancel-check.log. No warnings/errors in the full run.

All three public core theorems have named audits under the unchanged
propext/Classical.choice/Quot.sound allowlist. Source scans found no sorry,
admit, custom axiom or native_decide in the new core/changed fixture. Initial
fixture elaboration required correcting a substituted variable name and stating
the zero-division counterexample existentially before dependent elimination;
both were resolved before the full run. `git diff --check` passed.

The targeted rewrite is bidirectional in actual ConditionalValue semantics for
all coordinates/results. The fixture retains its independent original-expression
value-one proof, computes a successful rewritten cover, and transports the full
SoundOn contract back to the original partial coordinate relation. Endpoint
existence, zero exclusion and the coordinate hole are checked. Negative controls
preserve undefined guards, an active false-branch pole at equality and unknown
checking, and reject unguarded self-division by zero. Prior genuinely unbounded
pole/no-finite-cover tests continue to pass.

Rule selection is explicit; there is no automatic matcher, general simplifier,
evaluator replacement, FP assumption change, application change or merge.


<!-- Historical material from PR #45; original milestone claims and validation follow unchanged. -->

## Numerical nonzero-domain certificates (2026-11-07)

Based on merged main `8ce2199f6d2d72c0c47269d02b8e1f1aa8cde7f0`, independently
of pending #44. `./check.sh` passed: full Lean build, standalone enforced audit,
579 named audit commands, 1,102 imported namespace theorem/axiom declarations,
60 root modules, and all 14 Python enforcement/integration tests. The registry
now runs five fresh core-only semantic fixtures. The new NonzeroDomains fixture
also passed focused elaboration and namespace auditing (19 declarations), with
no warnings. Full log: `/workspace/lean-tools/nonzero-domains-check.log`.

Controls cover the exact punctured reciprocal domain, exclusion at the pole,
unknown whole-hull reciprocal evaluation, independent partial-expression
semantics, indistinguishable zero-only/one-only relations under loose bounds,
and preservation of absent input domains. Three new public core theorems have
named audits. Allowlist unchanged: `propext`, `Classical.choice`, `Quot.sound`.
No proof placeholders, new axioms, or native proof shortcuts were added.
`git diff --check` passed. No application, FP assumptions or hosted CI changes.

## Public-operation coverage and finite basic operations (2026-11-07)

Baseline: merged main `3975a5e1696e59c337093435ffce0748f074a057`.
This proof branch inventories all 58 public functions across four headers;
`OPERATION_COVERAGE.md` records header blob IDs and distinguishes merged proofs,
new branch proofs, evaluator integration, domain limitations and future C/IEEE
refinement. Historical integration receipts above are not rewritten.

`BasicIntervalOps` adds six finite rational operations and eight named theorems.
`lake build BasicIntervalOps` exited 0. The fresh independent fixture exited 0
and its namespace audit passed 21 theorem/axiom declarations, covering source
examples, sign/zero cases, whole-box composition, hull-vs-union and shared-boundary
intersection. Both header-ledger Python controls passed. Local file-link targets
in the four changed/new guide files passed (177 checked). `git diff --check` passed.

Environment recovery: the resumed workspace lacked the pinned mathlib checkout.
The exact pinned source `c44e0c8ee63ca166450922a373c7409c5d26b00b` was restored from
its public Git repository. The normal cache downloader could not write its default
home-cache path; a workspace-local XDG cache fixed that filesystem issue. Cache
requests to `https://lakecache.blob.core.windows.net/mathlib4` then returned HTTP
403 (0 of 6,641 downloaded). Those requests were not retried or redirected around
the restriction. Compilation proceeded locally from the pinned source instead;
no dependency pins or floating-point assumptions changed.

Full `./check.sh` then exited 0: Lake build, standalone audit (680 named checks,
1,272 namespace theorem/axiom declarations), and all 16 Python tests in 155.726s.
There are 72 registered library roots and 24 fresh semantic fixtures. No warnings
or errors were reported. The existing negative audit controls still reject sorry
and custom axioms; the allowlist remains propext/Classical.choice/Quot.sound.

During the run, documentation was extended following John's request to reference
both thesis and code as work proceeds: each coverage row now links its C
implementation and identifies a source lead or missing source proof. The ledger
parser was adjusted for those links and both inventory controls were rerun
successfully. Final guide checks passed 179 local file-link targets and verified
all referenced thesis/paper Markdown anchors against the pinned repository copies.
Only explicitly identified PDF checks assert precise source correspondence.
Final `git diff --check` passed. The prebuilt cache remains unavailable (403), but
local source compilation resolved the build blocker without bypassing restrictions.

## 2026-11-08: monotone endpoint bounds and floor/ceiling

Based on PR #69 head `bb363632581a79259dba29790c2e57701cce48a3`, branch
`proof/monotone-integer-bounds`. New core and fresh semantic fixture compiled
individually. Full `./check.sh` exited 0: Lake build, standalone audit with
686 named checks and 1,282 namespace declarations, and all 16 Python tests in
165.170s. There are 73 registered library roots and 25 semantic fixtures; the
new fixture audits 17 declarations. The unchanged allowlist is propext,
Classical.choice and Quot.sound. Negative audit controls passed.

The fixture checks the source floor example, negative inputs, integer endpoints,
least-enclosure versus discrete-image distinction, discontinuity, antitone bounds
and whole-box exclusion. No evaluator syntax, C implementation or FP assumptions
changed. Full output is retained locally at
`/workspace/lean-tools/integer-bounds-check.log`.

The subsequent documentation-only source assessment visually checked thesis PDF
pp. 35–36 and 48–49 for the Tupper-first FP gap map. No new mathematical claim
or FP assumption was introduced by that assessment.

## 2026-11-08: first compiled hardware interval addition

Branch `proof/hardware-directed-addition` preserves the preceding monotone-bound
commit and adds an explicitly conditional hardware result theorem. The unchanged
Lean 4.19.0 toolchain built the complete library and passed the standalone axiom
audit: 688 named checks and 1,288 namespace declarations. There are 75 registered
library roots and 26 fresh semantic fixtures. The new fixture independently
passed its four-declaration audit. No new axiom was added.

The initial `./check.sh` ran all 16 Python tests in 120.556s: 15 passed, and the
module-inventory test correctly rejected the new nested executable client. The
policy was updated to inventory exactly `hardware/Main.lean`, while still rejecting
other unregistered nested sources. The complete affected test then passed in
58.368s (`python3 -m unittest discover -s tests -p test_project_integration.py
-k all_modules -v`). Proof files were unchanged after their successful audits.
This is validation across the initial run and focused correction, not a claim
that the original full command exited zero.

`./hardware/check.sh` exited 0 on x86_64 using GCC 14.2.0 for the adapter and
the pinned Lean compiler for the executable. The adapter object contained hardware
`addsd`. Compiled Lean assertions passed for positive/negative halfway sums,
interval corners, subnormals, signed cancellation, overflow/infinity/NaN unknowns,
and environment restoration (four rounding modes and exception flags). The final
run additionally checked unknown under FTZ/DAZ. These are empirical observations,
not proofs of the adapter contract or C/FFI refinement.

Logs: `/workspace/lean-tools/hardware-add-full-check.log` and
`/workspace/lean-tools/hardware-add-execution.log`. Documentation checks passed
205 local file targets; final diff whitespace checks passed. Remote main was
rechecked at `4e8a8f4` (PR #69 merged); its Lean tree exactly matches the validated
base `bb36363`. No application build, hosted CI, toolchain pin or FP error/ULP
assumption changed. The native IO extern is outside proof checking; its throwing
logical fallback is not claimed equivalent to the native implementation.

## 2026-11-08: PR #70 final-head qualification

The independent review requested a clean full run instead of relying on the
preceding split result. `./check.sh` was rerun against reviewed code head
`81c857a06f4d0a56f073dd3452fdbf1ab9ad7f83`. This qualification changes documentation
only; no Lean proof, runtime source, build script or test policy changed.

The complete `./check.sh` exited **0**: Lake build, standalone axiom audit
(688 named checks; 1,288 namespace declarations), and all 16 Python tests
in 173.114s, including all 26 fresh semantic fixtures and audit-negative controls.
This clean result supersedes the earlier split-run qualification.

Actual toolchain output from the same environment:

```text
cc (Debian 14.2.0-19) 14.2.0
clang version 15.0.1 (https://github.com/llvm/llvm-project b73d2c8c720a8c8e6e73b11be4e27afa6cb75bdf)
Target: x86_64-unknown-linux-gnu
Thread model: posix
InstalledDir: /workspace/lean-tools/lean-4.19.0-linux/bin
Lean (version 4.19.0, x86_64-unknown-linux-gnu, commit 6caaee842e94, Release)
```

Here `cc` compiles the adapter with `-O2 -frounding-math -fno-fast-math
-ffp-contract=off`; `leanc --version` produces the Clang output above, and leanc
compiles/links the generated Lean executable. `./hardware/check.sh` was also
rerun and exited 0, detecting `addsd` and passing all nine reported native checks,
including the environment/FTZ/DAZ controls. No compiler-version inference is needed.

Full logs are retained locally as `hardware-add-final-check.log`,
`hardware-add-final-native.log`, and `hardware-add-final-toolchains.log` under
`/workspace/lean-tools`. The concordance now records the original-PDF mismatch in
§3.1.4's asymmetric-error labels (printed pp. 46–47), with elementary counterexamples;
no current proof uses those printed formulas.

## 2026-11-08: hardware-directed subtraction

Based on merged PR #70, main `ee964e6272bf04b665165d1dc37bddb569f7a48c`, branch
`proof/hardware-directed-subtraction`. The operation reuses the existing endpoint
representation and assembly, and shares native rounding/environment handling with
addition. The new proof is conditional on observed subtraction-call contracts;
no decoder, FFI or physical-hardware verification is claimed.

A clean full `./check.sh` exited **0**: Lake build, standalone audit (689 named
checks; 1,289 namespace declarations), and all 16 Python tests in 170.631s.
There are 76 library roots and 27 fresh semantic fixtures. The new four-theorem
fixture independently passed before the full run. The allowlist is unchanged.

The final `./hardware/check.sh` exited **0**, requiring both `addsd` and `subsd`
in the adapter object and passing all 18 reported native checks. Nine subtraction
checks exercise crossed endpoints, positive/negative midpoint rounding, the
midpoint just below one, subnormal difference, signed cancellation and unknown
on overflow/infinity/NaN. Existing addition checks remain. Both operations are
checked for environment restoration across four rounding modes, exception-flag
preservation and FTZ/DAZ rejection. These are empirical controls, not a proof of
the adapter contract.

Actual compilers: `cc (Debian 14.2.0-19) 14.2.0`; `leanc --version` reports Clang
15.0.1 (`b73d2c8c720a8c8e6e73b11be4e27afa6cb75bdf`), targeting
`x86_64-unknown-linux-gnu`; Lean remains 4.19.0 (`6caaee842e94`). No pin changed.
Logs are `/workspace/lean-tools/hardware-sub-full-check.log`,
`hardware-sub-native.log` and `hardware-sub-toolchains.log` in the same directory.

Tupper §3.2.22 (printed p. 64 / repository PDF p. 80) was visually checked against
the source inventory. The operation guide links that source and the pinned C
implementation, and prioritizes remaining API work. Documentation checks passed
200 local file targets; `git diff --check` passed. Only a runtime comment and
documentation changed after the full check started; the final native check was
rerun after that comment edit. No mathematical assumptions, application code,
release dependency or hosted CI changed.

## 2026-11-08: multiplication foundation, selection decision pending

Branch `proof/hardware-multiplication-foundation` starts at PR #71 head
`f636155806a16ba8b0b02f8b32790ad2b36cded3`. It reuses the real four-product lemma,
proves rounded-corner and selected-outer-bound consequences, and demonstrates
native directed corner products. It does not install a native selector or claim
a completed hardware interval multiplication operation. The proposed finite
comparison/selection contract remains unadopted, pending parent/user review.

Clean full `./check.sh` exited **0**: library build, standalone allowlist audit
(692 named checks; 1,292 namespace declarations), and all 16 tests in 171.997s,
including 28 fresh semantic fixtures. There are 77 library roots. The source-example
fixture was extended before the full run reached the fresh-fixture phase; that
final fixture was checked by the successful full run. The same final native client
was separately rebuilt and executed successfully: all 25 reported checks passed,
including observed hardware `mulsd`, nonexact products, both signs of underflow,
overflow and zero/infinity unknowns, and the thesis example's four corner products.

No selector correctness was assumed in these checks or proofs. The new selected-
bounds theorem takes real inequalities as explicit proof obligations and does not
assert them about native Float comparison. See `HARDWARE_MULTIPLICATION.md` for the
precise proposed additional contract and the representation-model alternative.

Compiler versions remain GCC 14.2.0 for the C adapter, leanc's Clang 15.0.1, and
Lean 4.19.0. Actual output and complete logs are retained in
`/workspace/lean-tools/hardware-mul-foundation-{toolchains,check,native}.log`.
The repository PDF's printed pp. 67–68 were visually checked. File links in the
new guide and final diff whitespace checks passed. No new axiom, application build,
toolchain pin, hosted CI, or extra FP assumption was introduced.

## 2026-11-08: completed multiplication with approved finite selection

John approved finite native min/max ordering in the adapter contract after reviewing
its relationship to IEEE 754 and Tupper §3.1.1. The previous foundation record above
remains a historical snapshot. This completion adds the shared executable
`assembleFour` and its enclosure theorem under four multiplication-call contracts
and two finite selector contracts. No new axiom or toolchain change was introduced.
The branch remains stacked on PR #71 head `f636155806a16ba8b0b02f8b32790ad2b36cded3`.

Clean full `./check.sh` exited **0**: library build, standalone audit (693 named
checks; 1,294 namespace declarations), and all 16 Python tests in 212.246s.
There are 77 library roots and 28 fresh semantic fixtures. The multiplication
fixture independently passed its seven-declaration audit, including application of
the assembled theorem, rejection of a bad minimum selector and all four missing-
corner positions. No mathematical source changed after this full check started.

The compiled native check exited **0**, passing all 29 reported checks. The former
point-only multiplication helper was replaced by the complete interval operation.
Tests include mixed-sign and negative intervals, the source `[-2,3] × [5,7]` example,
nonexact products, both signs of underflow, and unknown when just one corner
overflows. The raw-corner checks, addition/subtraction regressions and environment
controls remain. The adapter object contains `mulsd`; finite min/max selection runs
in compiled Lean. Native tests do not prove the decoder, FFI, compiler or hardware.

Actual compiler versions were recorded again: GCC 14.2.0 (Debian 14.2.0-19) for
the adapter, leanc's Clang 15.0.1 (`b73d2c8c720a8c8e6e73b11be4e27afa6cb75bdf`),
and Lean 4.19.0 (`6caaee842e94`), on x86_64. Logs are
`/workspace/lean-tools/hardware-mul-{full-check,native,toolchains}.log`.

The original PDF's printed p.45 / PDF p.61 was visually checked: §3.1 assumes IEEE
754 and §3.1.1 lists min/max as exact functions. The current guide documents the
approved finite-only interpretation, excluded NaNs, signed-zero tie freedom, and
remaining implementation trust boundary. Checks passed 197 local documentation
targets and final diff whitespace checks. No application code or hosted CI changed.

## 2026-11-08: multiplication exception-restoration control

Independent review requested an actually inexact multiplication in the environment
probe. Each of the four ambient modes now first evaluates volatile
`2^-1074 × 0.5` and requires both FE_UNDERFLOW and FE_INEXACT to be raised. After
clearing those flags and establishing FE_INVALID as the caller state, the directed
wrapper repeats that underflowing multiplication and must restore exactly the
caller flags and rounding mode. The probe holds exceptions while testing and
restores the original environment on exit.

`./hardware/check.sh` exited 0 with all 29 checks passing, including this strengthened
control. Log: `/workspace/lean-tools/mul-restoration-strengthened.log`. Only the
native test probe changed; mathematical definitions and proofs are unchanged from
the clean full run above. Final `git diff --check` passed.

## 2026-11-08: finite guarded hardware division

Built on PR #72 head `a8190fbff7f7d131f8068a1f8c29c960a8434f77`, preserving its
strengthened underflow restoration probe. `HardwareDivision` proves strict zero
exclusion, real four-quotient bounds and conditional assembled enclosure together
with denominator nonzero. The generic decoded hull helper is shared with the
existing multiplication theorem; its public statement is unchanged. Finite
comparison agreement and zero decoding are explicit representation obligations;
there are no new axioms, error budgets or toolchain changes.

`./hardware/check.sh` passed all 40 native checks. The adapter object contains
`divsd` as well as the earlier add/sub/mul instructions. New cases include either
sign of denominator, rounded 1/3, signed underflow, zero-touch/cross rejection,
partial overflow and exceptional inputs. The environment test directly establishes
that 1/3 raises INEXACT before checking restoration of caller flags and modes.
The independent semantic fixture passed its eight-declaration audit, including a
complete assembled theorem client and a deliberately incorrect comparator control.

Actual compiler versions: adapter GCC 14.2.0 (Debian 14.2.0-19); leanc Clang 15.0.1
(`b73d2c8c720a8c8e6e73b11be4e27afa6cb75bdf`), x86_64; pinned Lean 4.19.0.
Logs: `/workspace/lean-tools/hardware-div-{native,fixture,full-check}.log`.
The five updated scope guides passed checks of 214 local documentation targets.
The C public division implementation remains unverified and uses a different
reciprocal-then-multiply algorithm. No application code or hosted CI changed.

The final full `./check.sh` passed: library build, standalone enforced audit
(698 named checks, 1,301 namespace theorem/axiom declarations), and all 16 Python
tests in 179.180s. Coverage includes 78 library roots and 29 fresh semantic fixtures.
All mathematical/runtime source changes preceded this full run; subsequent edits
were documentation only. Final `git diff --check` passed.

## 2026-11-09: directed hardware square root

Fetched and verified main at `7fd4b39dc127dec3be1b96a46cf392d4bcd73d2b`, containing
merged PRs #70–#73, then branched `proof/hardware-square-root`. Repository and
ancestor instruction searches found no AGENTS.md or repository `.agents/skills`.
The resumed cloud runtime was ready; validation stayed on this executor and was
run sequentially rather than concurrently with a native build or on the Mac.

`HardwareSquareRoot` proves conditional endpoint enclosure after clipping the
lower input to zero, bridges the actual assembly to `SqrtValues` with unchanged
witness/domain restrictions, preserves incoming definedness on nonnegative bounds,
and proves absence from a certified negative upper bound. Runtime `none` still
means unknown. The existing approved directed IEEE primitive, finite max and zero
interpretation boundary is explicit; no new global axiom or FP error assumption.
The runtime returns bounds, not decorated domain flags or a new Expr evaluator.

Focused library compilation passed. An initial independent fixture attempt left
sqrt(4) normalization goals unresolved; the enforced audit rejected the resulting
sorryAx. The fixture was corrected with a proved sqrt(4)=2 lemma, then passed its
19-declaration namespace audit. Final fixtures include nonnegative/mixed assembled
enclosure, the SqrtValues bridge, retained external holes, negative-domain absence,
a totalized-root counterexample, wrong-primitive rejection and missing-result
unknown. Exact binary64 squaring checks independently qualify the sqrt(2), largest
finite and smallest-subnormal expected native bit patterns, without a sqrt library.
These rational checks are test oracles, not the executable interval backend.

`./hardware/check.sh` exited 0 with 54 reported native checks (40 regressions plus
14 square-root controls). The adapter object contains sqrtsd and no unresolved
library sqrt symbol. Tests include either domain branch and zero boundary, signed
zero, subnormal input, largest finite value, NaNs, infinities, reversed endpoints
and negative primitive rejection. Each ambient-mode restoration test first checks
that sqrt(2) raises INEXACT, then checks restoration of the caller's flags and mode.
All preceding hardware arithmetic regressions remain enabled.

Compilers: GCC 14.2.0 (Debian 14.2.0-19) for the adapter; leanc Clang 15.0.1
(`b73d2c8c720a8c8e6e73b11be4e27afa6cb75bdf`), x86_64. Lean 4.19.0 and mathlib pins
are unchanged. Native flags add `-fno-math-errno` so the guarded sqrt path uses the
hardware instruction without libm errno handling; this does not verify compilation.
Logs: `/workspace/lean-tools/sqrt-{build,fixture,native,full-check}.log`.

Review compared the proof and client call arguments (clipped lower, original
upper), optional-result behavior and signed-zero scope; independently checked
expected-bit enclosures by exact squaring; and visually checked thesis §3.1,
printed p.45/PDF p.61, and SIGGRAPH §8, PDF p.4, against the repository source copies.
C references are pinned to the verified base. C's negative-input empty result and
other architectures remain outside the proof. No separate reviewer is claimed.
The five updated scope documents passed checks of 220 local link targets. No
application code, hosted CI or toolchain changes were made.

Final full `./check.sh` exited 0: library build, standalone audit (702 named
checks, 1,305 namespace declarations), and all 18 Python tests in 241.928s.
Integration coverage includes 79 library roots and 30 fresh semantic fixtures.
All proof/runtime/test sources preceded this full run; only documentation changed
after it began. Final diff whitespace check passed. No push or merge of unrelated
work is part of this milestone.

## 2026-11-09: square root on the published standalone GIA baseline

The actual public gia main was fetched and verified at
`1f67388d6e11a3eb3677900fd9826899433935e1`, with sole parent
`5205f7794e34d6841b7bd3bd6e9898caaf743ab1`. Compared with the local migration
baseline, differences were exactly LICENSE, COPYRIGHT, README.md, THIRD_PARTY.md
and MIGRATION.md, and their diffs matched the owner-applied license/documentation
changes. The MIT LICENSE blob remains identical to the initial gia commit.

The separate square-root review preserves all 110 Lean source files byte-for-byte
from relgraph #74 head `f7cfea863529e48dffddc393cb9fb25d41ea9b03`. LICENSE,
COPYRIGHT and SCOPE.md remain byte-identical to published gia main. No mathematical
scope or floating-point assumption changes were introduced. Current migration
framing was corrected without rewriting historical validation receipts. Original
relgraph #74 is not merged or closed by this transfer.

All 330 local documentation targets passed; explicit optional API comparison
passed five tests, including changed/missing-header controls. Full qualification
uses only the existing cloud Lean/mathlib caches, sequentially with native checks;
no Mac workload or hosted CI is added. Logs are in `/workspace/gia-followup`.

Final full `./check.sh` exited 0: 702 named audits, 1,305 namespace declarations,
79 roots, 30 fresh semantic fixtures, and 21 tests in 321.856s (only the optional
checkout comparison skipped; it passed separately when explicitly enabled).
`./hardware/check.sh` exited 0 with all 54 native checks. GCC 14.2.0
(Debian 14.2.0-19), leanc Clang 15.0.1, and Lean 4.19.0 remain unchanged.
All proof/runtime/test changes preceded this run; later edits were documentation
only. Final diff whitespace checks passed.

## 2026-11-09: hardware sine on [0, 1]

Base: GIA main `a6cb4c8b5d1dd00dc836b3f98eb91409d60efd9e`.
The milestone is described in [HARDWARE_SINE.md](HARDWARE_SINE.md).

- Full `RELGRAPH_CHECKOUT=/workspace/gia-followup/relgraph-removal ./check.sh`
  exited 0. The pinned Lean build and fresh audit passed. All 21 Python tests
  passed in 348.820s, with no skips; the explicitly supplied C checkout matched
  the pinned header inventory. All 82 library roots and 31 fresh semantic
  fixtures were covered.
- Enforced axiom audits passed 712 named checks and 1,320 theorem/axiom
  declarations in the project namespace. Only `propext`, `Classical.choice`
  and `Quot.sound` are permitted. New sine fixtures passed their own audit
  of 28 declarations. No `sorry` or new axiom is used.
- `./hardware/check.sh` exited 0: the 54 prior native checks passed, together
  with six unsupported-input controls, one injected division-failure control,
  and 39 supported sine vectors. The independent exact-arithmetic oracle
  checked the observed binary64 results against directed arithmetic and
  analytic enclosures; it did not call libm sine. The adapter disassembly
  retained the checked hardware arithmetic/square-root instructions.
- Observed native point widths, including rounding: 0 at x=0;
  1.5500992064931829e-6 at x=1/2; 0.00019841269841303077 at x=1.
  The proved analytic width is x^7/5040, at most 1/5040; this is not a bound
  on the final interval width, which also includes rounding and dependency.
- A separate source/specification review compared the PDF's printed pp.48–49,
  the partial-domain relation, the range guard, all primitive-to-interval
  contracts, and the shared pure/IO program. An exact-real Lean client checks
  both point 1 and the whole [0, 1] interval. This does not replace independent
  PR review or prove native IO/FFI/compiler refinement.
- Lean 4.19.0; mathlib remains pinned at
  `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
  Native compiler: GCC `cc (Debian 14.2.0-19) 14.2.0`;
  `leanc` uses Clang 15.0.1, on x86_64.
- The public mathlib cache endpoint returned HTTP 403 under the environment's
  network policy. It was not retried or bypassed; the missing dependencies
  were successfully built from the pinned local source instead.

The adapter C file, toolchain pin, dependency manifest and license files are
unchanged. Mathematical bounds and enclosure composition are kernel-checked;
finite decoding, directed primitives, comparison and native refinement remain
explicit adapter obligations. No correctly rounded sine, argument reduction,
full IEEE verification or correspondence to relgraph's MPFR sine is claimed.

## Signed sine endpoints — 2026-11-10

Based on gia main `bb937fa47b22ebb10a77a97fdbb1b10843cf6a35`, which already
contains merged PR #2. This milestone adds `SineEndpoints.lean`, the shared
`signedPoint` / `endpoints` programs, the native client and independent controls.

- Full `RELGRAPH_CHECKOUT=/workspace/gia-followup/relgraph-removal ./check.sh`
  exited 0. All 21 tests passed in 193.893s, with no skips, including the explicit
  C API-header comparison, 83 registered library roots, and 32 independently
  compiled semantic fixtures. The rejected-axiom controls remain enabled.
- Enforced audits passed 720 named checks and all 1,328 project-namespace
  theorem/axiom declarations. Only `propext`, `Classical.choice` and `Quot.sound`
  are allowed. No `sorry`, custom axiom or native proof evaluation is introduced.
- Final `./hardware/check.sh` exited 0. All baseline checks passed, plus six new
  unsupported-input controls and three injected failures (reflection, positive
  evaluator, upper endpoint). The oracle checked 39 original natural-interval
  vectors and 73 signed endpoint vectors. Each signed vector matched independent
  exact directed-operation simulation and enclosed nine analytic samples from
  a distinct higher-order alternating-series bound, without calling libm sine.
- Observed [0, 1] native widths: natural interval 1.175198412698413;
  monotone endpoints 0.8416666666666668. Nonnegative signed-vector cases were
  also checked for inclusion in the old native bounds. This is finite test
  evidence, not a universal native precision theorem. The pointwise analytic
  Taylor width remains |x|^7/5040; no correctly rounded sine is claimed.
- A separate specification/diff review checked the pure/IO shared control flow,
  comparison guard, directed reflection, endpoint ordering, partial-domain
  semantics, and source correspondence. Lean controls include signed composition
  through an independent exact-real oracle, an external hole, failure cases and
  the counterexample to global monotonicity. This local review and independent
  oracle testing do not replace independent human PR review or FFI verification.
- Tupper's original PDF printed pp.56–57 was visually checked for §3.2.10's
  monotone endpoint argument and §3.2.12's lower-bound construction. The existing
  §3.1.6 Taylor correspondence remains unchanged. The present claim is restricted
  to real sine on [-1, 1], not the full generalized-domain source treatment.
- Local links in the four edited entry/topic/concordance documents were checked;
  `git diff --check` passed. The FFI adapter, toolchain pin, dependency manifest,
  license and copyright files are byte-for-byte unchanged.
- Lean 4.19.0; mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`;
  GCC `cc (Debian 14.2.0-19) 14.2.0`; leanc Clang 15.0.1; x86_64.
  Missing trigonometric dependencies were built from the pinned local source.
  The previously denied cache endpoint was not retried or bypassed.

No floating-point trust-boundary change: negative reflection uses existing
directed subtraction. Exact decoding of -1 is another instance of the existing
small-constant decoding obligation. Finite decoding, ordering, primitive rounding,
and IO/FFI/compiler/hardware refinement remain explicit assumptions. Unsupported
ranges and failures remain unknown; no argument reduction, general transcendental
library, C-implementation verification or hosted CI is added.

## Certified pi and finite period reduction — 2026-11-10

Base: merged gia main `9ea7d9d13035805a4b3a9f382b4310b808b8f4e9` (PR #3).
The merge was head-guarded at `a36efb893f807c002784a4764f2fced8b8341cca`;
its resulting tree matched the qualified PR head exactly.

- Full `RELGRAPH_CHECKOUT=/workspace/gia-followup/relgraph-removal ./check.sh`
  exited 0. All 21 tests passed in 212.221s with no skips, including explicit
  C header/inventory comparison, all 86 registered library roots and 33 fresh
  semantic fixtures.
- Enforced audits passed 728 named checks and 1,347 project-namespace
  theorem/axiom declarations (including generated program helper theorems).
  The new fixture separately passed its 16-declaration namespace audit. Only
  `propext`, `Classical.choice` and `Quot.sound` are allowed; no custom axiom,
  `sorry` or native proof evaluation was introduced.
- Final `./hardware/check.sh` exited 0. It retained the 39 original sine and
  73 signed-endpoint vectors and all previous primitive checks, and added
  92 period-reduction vectors, seven rejection controls and an injected
  multiplication failure. The adapter instruction and environment-restoration
  checks passed.
- The independent oracle checked the actual pi bit patterns against rational
  Machin-formula bounds and the exact width 2^-51. Every reduced native result
  matched an exact directed-operation simulation. Nine samples per interval
  were independently checked using a sine series at the ORIGINAL input, not
  the reduced argument; this check does not depend on pi or the runtime
  reduction formula. Test-only rational arithmetic is not used by the runtime.
- Lean proved strict dyadic pi containment from pinned mathlib bounds,
  successful integer-period reduction, finite-search soundness, the concrete
  candidate list and the existing signed kernel's contract. Controls cover
  an independent exact-real composed client, retry/exhaustion/failure,
  external holes and the invalid exact-singleton pi approximation.
- A separate local specification/diff review checked propagation of pi
  uncertainty, the common input witness, integer candidate certificates,
  native/pure shared control flow, exceptional handling and documented scope.
  Tupper §3.1.5, printed pp.47–48, was visually checked in the authorized
  repository PDF. The Markdown quarter/half-offset transcription defect is
  documented; this implementation uses whole-period search, not that formula.
  This local review and oracle testing do not replace independent human PR
  review or verification of the compiled implementation.
- Local Markdown links and `git diff --check` passed. FFI adapter C, toolchain,
  dependency lockfile, license and copyright files are byte-for-byte unchanged.
  No hosted CI was added. Missing pi-bound dependencies were built from pinned
  local mathlib source; the previously denied cache endpoint was not retried.
- Lean 4.19.0; mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`;
  GCC `cc (Debian 14.2.0-19) 14.2.0`; leanc Clang 15.0.1; x86_64.

The runtime tries only periods 0, +1, -1, +2, -2 and requires each successful
residual interval to fit [-1, 1]. For example, [6, 6.5] and [12.25, 12.75] pass;
1.5, [0, 7] and 100 remain unknown. Coverage is not continuous across the full
span, and no all-finite-argument reduction or correctly rounded sine is claimed.
There is no new FP contract: exact decoding is instantiated for the two specified
pi dyadics and small integer coefficients; ordering, directed primitives and
IO/FFI/compiler/hardware refinement retain their existing trusted status.

## Certified cosine and quadrant cover (2026-11-11)

Qualified against merged main `eef2d07b34edfcd6dad9e41a302092c2179c01bd`.

- Full `./check.sh`, with the optional pinned relgraph checkout comparison,
  passed: 21 tests in 223.868 seconds, no skips. Both audit passes accepted
  751 named checks and 1,440 project namespace declarations, using only
  `propext`, `Classical.choice` and `Quot.sound`. Inventory checks cover 92
  library roots and 34 semantic fixtures; the new fixture audits 19 declarations.
- Final `./hardware/check.sh` passed all prior 204 sine vectors, 68 cosine
  vectors and 149 quadrant vectors. The new independent exact directed-operation
  oracle matched native results; 17 original-input analytic samples per new
  vector passed. Whole [-4,4] returned exactly [-1,1]. Controls cover extrema,
  shared boundaries, adjacent floats, subnormals, unsupported inputs, late
  failure after earlier success, and environment restoration.
- The observed cosine point width at x = 1 was 2.4801587301892525e-05,
  including rounding, compared with the proved analytic budget 1/40320.
  Interval dependency and directed rounding may increase widths.
- A local specification review checked common witnesses, all-cell coverage,
  disjointness versus failure, negative phases, endpoint extrema and partiality.
  Independent Lean controls include the cosine endpoint-only counterexample,
  a composed exact-real client, and failure/external-hole controls. This is
  local review plus independent test oracles, not a second-agent or human review.
- Tupper §3.1.6 (printed p.48/PDF p.64) and §3.2.6 (printed p.54/PDF p.70)
  were visually checked in the authorized repository PDF. This construction
  follows the Taylor and cover methods; it is not a verbatim thesis formula
  or a claim of proper/minimal monotonicity partitioning.
- Local documentation links and `git diff --check` passed. Adapter C,
  toolchain, dependency lockfile, LICENSE and COPYRIGHT are unchanged.
  No hosted CI was added, and no denied source/cache access was retried.
- Lean 4.19.0; mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`;
  GCC `cc (Debian 14.2.0-19) 14.2.0`; leanc Clang 15.0.1; x86_64.

There are no new floating-point contract assumptions. Exact literal decoding,
finite comparisons/min/max, directed primitives and IO/FFI/compiler/hardware
refinement remain the existing trusted boundary. Lean proves geometric coverage
and enclosure on success, not unconditional success of every implementation
satisfying enclosure-only contracts. Unsupported inputs or primitive failures
remain unknown. No correctly rounded transcendental or full-range sine claim
is made. See [construction and limitations](HARDWARE_COSINE_QUADRANTS.md).

## Composed sine reduction and global fallback (2026-11-11)

Base: merged GIA #5, `d1caaafb7511d3fc3487e77c9600cc557d1224ee`.
The merge was verified against qualified head `56ee86126799e6bb0b42d32346baf9cdffa8995a`;
there were no tree changes or hosted checks.

- The full project build and both axiom-audit passes accepted 755 named checks
  and 1,445 namespace declarations with the existing standard axiom allowlist.
  No new axioms, `sorry`, or native proof evaluation were added.
- Final `./hardware/check.sh` passed all previous vectors and 267 new global
  sine vectors: 261 refined through period/quadrant composition, 6 used the
  proved global bound. The independent oracle matched directed operations and
  checked nine original-input series samples per interval inside [-16,16].
  Maximum-finite and huge intervals were checked against the exact fallback,
  not a huge-angle numerical oracle. NaNs, infinities, reversed inputs,
  injected refinement failure and environment restoration passed.
- The independent oracle needed explicit nonfinite-rounding rejection for the
  maximum-finite tests; its initial attempt raised Python OverflowError. That
  test harness limitation was corrected, then the complete native suite passed.
- Lean controls preserve refined results, reject unsupported input and prove
  the fallback sound for every real input. The updated independent reduction
  fixture audits 20 declarations. Source/diff review checked both reduction
  levels, common input witnesses, guards and fallback semantics.
- Tupper §3.1.5, printed p.47/PDF p.63, was visually rechecked in the repository
  PDF. The implementation composes certified integer shifts; it does not claim
  to implement the source's fractional-part formula. The damaged Markdown
  quarter-versus-half transcription was not used as authority.
- Adapter C, toolchain, dependency pins, LICENSE and COPYRIGHT are unchanged.
  No hosted CI or new FP assumptions were added. Lean 4.19.0 and pinned mathlib
  remain unchanged, as do GCC 14.2.0 and leanc Clang 15.0.1 on x86_64.

This is conservative all-finite-input handling, not precise full-range argument
reduction or correctly rounded sine. The global fallback has width 2. Pure
wrapper success is proved after an accepted guard; native IO termination and
refinement remain outside the proof. External domains are not enlarged.
See [scope and limitations](HARDWARE_SINE_GLOBAL.md).

Final complete `./check.sh` result: **21 tests passed in 352.166 seconds**, no
skips, including the explicit relgraph checkout comparison, 92 registered library
roots, all 34 fresh semantic fixtures and negative audit controls. Final local
Markdown checks covered 229 links; `git diff --check` passed.
