> Historical relgraph record: old paths and checks describe their original context.
> For the standalone layout and fresh verification, see [MIGRATION.md](MIGRATION.md).

# Lean integration plan

This is a review plan, not authorization to merge. Snapshot: 2026-11-07.
No PR was merged, rebased, retargeted or force-pushed during this assessment.
No hosted CI or floating-point assumption changes are proposed.

## Observed input heads

GitHub metadata for #44–#59 was checked: all open and unmerged at these heads.
The #47–#59 base SHAs exactly matched the predecessor heads; #44, #45 and
#46 target main at `8ce2199f6d2d72c0c47269d02b8e1f1aa8cde7f0`.
These are source identities, not review approvals or a promise that remote branches remain unchanged.

| PR | Base | Verified head |
| --- | --- | --- |
| [#44](https://github.com/funge/relgraph/pull/44) | main | `a3c38161bcba9a5b8c176f0551a6db6f94758ad4` |
| [#45](https://github.com/funge/relgraph/pull/45) | main | `9fb779e8843c317b30bdcca5097949c98083d43b` |
| [#46](https://github.com/funge/relgraph/pull/46) | main | `5af426f12b2dd6686524479633a2bc178332125f` |
| [#47](https://github.com/funge/relgraph/pull/47) | #46 | `00d1a4914e816da96ccee9449b05610602194556` |
| [#48](https://github.com/funge/relgraph/pull/48) | #47 | `404271d5b6e19c2df89825e4446afb5671c28548` |
| [#49](https://github.com/funge/relgraph/pull/49) | #48 | `a68996dfac7b4036d674e9d4327039221199e76f` |
| [#50](https://github.com/funge/relgraph/pull/50) | #49 | `ee23e8e49965bd474237806f55a9327467ed9de0` |
| [#51](https://github.com/funge/relgraph/pull/51) | #50 | `c385d0e08284c82429eca53beedde64edd2efdaf` |
| [#52](https://github.com/funge/relgraph/pull/52) | #51 | `9efa154bd09e8a9a2198974da6aaf1e37102746c` |
| [#53](https://github.com/funge/relgraph/pull/53) | #52 | `ba976a57f4060352efa1c1d0f283e2e8438e186e` |
| [#54](https://github.com/funge/relgraph/pull/54) | #53 | `8739adff1b4fd8169c03cc1634017d3fee88555c` |
| [#55](https://github.com/funge/relgraph/pull/55) | #54 | `e7c60ee7fd295ebe4630ff44bee400b0edced30a` |
| [#56](https://github.com/funge/relgraph/pull/56) | #55 | `ad579edf1a378a6dde1264770cca6f1373ba99cc` |
| [#57](https://github.com/funge/relgraph/pull/57) | #56 | `7b375e95ab5ff311f2c87759d78e9ac79b33194e` |
| [#58](https://github.com/funge/relgraph/pull/58) | #57 | `7ea8ab5ad52f84209159f461cccb057a5f230b5c` |
| [#59](https://github.com/funge/relgraph/pull/59) | #58 | `050ffd22c9ae0e4374045bbf599514966516c6d1` |

This documentation branch follows #59. Its eventual published head must be
qualified separately; a document cannot record its own commit hash in advance.
Native PR #31 and any other unrelated work are excluded.

## Actual overlap and dry-run conflicts

The core `NonzeroDomains.lean` in #59 is byte-identical to #45. It was deliberately
included in #47 as a prerequisite. Its import, three named theorem audits and Lake
library already occur in the chain. #45 additionally carries a separate
`tests/NonzeroDomains.lean` fixture and its registry entry, plus documentation.
Those additions must not be discarded just because the core is duplicated.

Git's tree-only three-way analysis was run on the exact heads above:

| Pair | Content-conflict files |
| --- | --- |
| #45 with #59 | Audit.lean, GENERALIZED_INTERVALS.md, INTEGRATION_ASSESSMENT.md, README.md, REVIEW_STACK.md, VALIDATION.md, lakefile.toml, tests/test_project_integration.py |
| #44 with #59 | Audit.lean, INTEGRATION_ASSESSMENT.md, REVIEW_STACK.md, VALIDATION.md, lakefile.toml |
| #44 with #45 | Audit.lean, INTEGRATION_ASSESSMENT.md, REVIEW_STACK.md, VALIDATION.md, lakefile.toml |

All paths are under `formalization/lean`. Each analysis returned exit 1 for
conflicts. This was `git merge-tree --write-tree LEFT RIGHT`: it created only
unreferenced tree objects and did not update refs, index or worktree. It neither
merged a PR nor produced a validated resolved tree. Even files Git can combine
automatically require semantic review. Logs are in the session scratch directory
`/workspace/lean-tools/merge-review/`; reproduce with the qualified head hashes.

## Compatibility evidence and its limits

The #59 full build, audit and fixture results are recorded in
[VALIDATION.md](VALIDATION.md). Additional checks used original source bytes
extracted with `git show`, outside the checkout, against #59's built libraries:

- #45's separate NonzeroDomains fixture passed and audited 19 declarations.
- #44's GuardedSimplification module compiled in an isolated import overlay.
- #44's original ThresholdCertificates fixture passed and audited 70 declarations.
- All three #44 public theorem audits passed with only the existing allowlist:
  `propext`, `Classical.choice`, `Quot.sound`.

The overlay adds the compiled GuardedSimplification module to the Lean import
path; it does not replace existing #59 modules. These targeted checks establish
source-level compatibility for those clients. They do not check combined Lake
registrations, final audit-import coverage, documentation resolution, or the full
resolved integration tree. There is no claim that the conflict set for the
three-way union equals the pairwise sets above.

## Proposed order after separate authorization

1. Re-read current main and every PR's state, exact head, base, reviews and checks.
   Verify the remote is exactly `https://github.com/funge/relgraph.git`. Fetch the
   qualified objects normally; this checkout need not have a local main branch.
   Stop for changed/unqualified heads, unrelated changes or unexpected failures.
2. Integrate #46 through #59 in dependency order, followed by separately reviewed
   descendants such as this documentation PR. Preserve commit ancestry: do not
   squash or rebase the chain. Before retargeting a successor to main, verify its
   predecessor is reachable from main and its remaining diff is the reviewed
   milestone. Retargeting is a future authorized action, not something done here.
3. Integrate #45 into the resulting chain on a reviewable preparation branch.
   Keep the byte-identical core, import, library and three named audits once.
   Add the original separate fixture and registry entry. Reconcile documentation
   by preserving historical receipts and both useful explanations; update current
   entry points. Do not resolve all files with a blanket ours/theirs choice.
4. Integrate #44 on that prepared result. Add GuardedSimplification, its import,
   one library registration and three named audits. Preserve the #44 threshold
   fixture extensions and the current fixture registry. Review automatically
   combined README/conditional documentation as well as explicit conflicts.
5. Run the full local `./check.sh` on each resolved integration milestone,
   inspect `git diff --check`, local Markdown links, file inventory and final
   diff against the expected union. Confirm no duplicate library names, dropped
   fixture registrations, lost audit imports, changed proof sources or rewritten
   historical validation. Record the exact resolved tree and commit being approved.
6. Only merge qualified results under the later authorization, verify each
   remote outcome and main reachability, and stop on discrepancies. If conflict
   resolution changes a PR head, that new head needs review and validation; the
   hashes in this snapshot no longer qualify it automatically.

#45 then #44 is a proposed order, not a mathematical dependency between them.
The important ordering constraint is the #46–#59 chain. Resolving the independent
branches after the chain avoids rewriting each descendant and makes their
remaining additions explicit. Actual conflict resolution may require a separately
reviewed integration PR; this plan does not authorize bypassing that review.

## Thesis-aligned next decisions

The [concordance](THESIS_CONCORDANCE.md) remains the source of truth for coverage.
The [consolidation assessment](INTEGRATION_ASSESSMENT.md#domain-and-search-consolidation-2026-11-07)
distinguishes domain evidence, ranges and root detection. Keep those contracts
separate: point completeness does not extend to uncertain interval inputs,
affine region certificates do not include arbitrary holes, and finite search
does not imply convergence.

Prioritize a precise chapter-2 inclusion or domain-property statement already
identified in the concordance, compare its original hypotheses and conclusion,
then formalize the smallest missing proof. Authorized graphing-repository PDF copies are now available, with a targeted
visual comparison recorded in the updated concordance. Do not retry or bypass
denied website PDF/GIF access. The next proof should use a precisely inspected
statement, preserving the separate thesis and 2001-paper tracks. No new
floating-point model is needed for this plan.



## Refreshed local rehearsal through PR 68 (2026-11-07)

This snapshot supersedes the earlier plan only for the listed heads. It does not
merge, retarget or change any PR. Main is 8ce2199f6d2d72c0c47269d02b8e1f1aa8cde7f0.
Native PR #31 is excluded. The local property-options commit is also excluded.
All listed source diffs are confined to formalization/lean.

| PR | Exact head | Current base branch | Exact base |
| --- | --- | --- | --- |
| #44 | `a3c38161bcba9a5b8c176f0551a6db6f94758ad4` | main | `8ce2199f6d2d72c0c47269d02b8e1f1aa8cde7f0` |
| #45 | `9fb779e8843c317b30bdcca5097949c98083d43b` | main | `8ce2199f6d2d72c0c47269d02b8e1f1aa8cde7f0` |
| #46 | `5af426f12b2dd6686524479633a2bc178332125f` | main | `8ce2199f6d2d72c0c47269d02b8e1f1aa8cde7f0` |
| #47 | `00d1a4914e816da96ccee9449b05610602194556` | feat/executable-domain-queries | `5af426f12b2dd6686524479633a2bc178332125f` |
| #48 | `404271d5b6e19c2df89825e4446afb5671c28548` | feat/automatic-quotient-domains | `00d1a4914e816da96ccee9449b05610602194556` |
| #49 | `a68996dfac7b4036d674e9d4327039221199e76f` | feat/exact-point-domains | `404271d5b6e19c2df89825e4446afb5671c28548` |
| #50 | `ee23e8e49965bd474237806f55a9327467ed9de0` | test/uncertain-domain-feasibility | `a68996dfac7b4036d674e9d4327039221199e76f` |
| #51 | `c385d0e08284c82429eca53beedde64edd2efdaf` | test/shared-environment-prototype | `ee23e8e49965bd474237806f55a9327467ed9de0` |
| #52 | `9efa154bd09e8a9a2198974da6aaf1e37102746c` | feat/affine-domain-guards | `c385d0e08284c82429eca53beedde64edd2efdaf` |
| #53 | `ba976a57f4060352efa1c1d0f283e2e8438e186e` | feat/affine-segment-domains | `9efa154bd09e8a9a2198974da6aaf1e37102746c` |
| #54 | `8739adff1b4fd8169c03cc1634017d3fee88555c` | docs/thesis-concordance | `ba976a57f4060352efa1c1d0f283e2e8438e186e` |
| #55 | `e7c60ee7fd295ebe4630ff44bee400b0edced30a` | feat/affine-segment-domain-completeness | `8739adff1b4fd8169c03cc1634017d3fee88555c` |
| #56 | `ad579edf1a378a6dde1264770cca6f1373ba99cc` | feat/affine-presence-domain-bridge | `e7c60ee7fd295ebe4630ff44bee400b0edced30a` |
| #57 | `7b375e95ab5ff311f2c87759d78e9ac79b33194e` | feat/affine-external-domain-checks | `ad579edf1a378a6dde1264770cca6f1373ba99cc` |
| #58 | `7ea8ab5ad52f84209159f461cccb057a5f230b5c` | feat/affine-region-segment-search | `7b375e95ab5ff311f2c87759d78e9ac79b33194e` |
| #59 | `050ffd22c9ae0e4374045bbf599514966516c6d1` | feat/affine-region-subdivision | `7ea8ab5ad52f84209159f461cccb057a5f230b5c` |
| #60 | `7c1997d5b785bf7b5cf9d3063b9a0cabb4706cc1` | test/domain-search-integration | `050ffd22c9ae0e4374045bbf599514966516c6d1` |
| #61 | `be6fc0b2f4b438aa391597f5585bc77b1a0b6e6d` | docs/lean-merge-plan | `7c1997d5b785bf7b5cf9d3063b9a0cabb4706cc1` |
| #62 | `3b317c38df9cbeb482df7e18db3670bd23f01898` | docs/thesis-paper-source-map | `be6fc0b2f4b438aa391597f5585bc77b1a0b6e6d` |
| #63 | `4845d6bd2f2d53ea1fa44ed65b9500c456c54d70` | proof/affine-coefficient-correspondence | `3b317c38df9cbeb482df7e18db3670bd23f01898` |
| #64 | `d8b7352aa8bc7e203e1142a4719c3f259ed346de` | proof/constant-interval-embedding | `4845d6bd2f2d53ea1fa44ed65b9500c456c54d70` |
| #65 | `e2c806c09b043cda292c1b176cfe0db35bacf902` | proof/quadratic-chord-corrections | `d8b7352aa8bc7e203e1142a4719c3f259ed346de` |
| #66 | `35eec824008be8f9bd9510431f74f4c94b1a0bf2` | proof/two-parameter-affine-order | `e2c806c09b043cda292c1b176cfe0db35bacf902` |
| #67 | `59d376a668e142b69051ab6cd46bfbff9b30df94` | proof/universal-input-domains | `35eec824008be8f9bd9510431f74f4c94b1a0bf2` |
| #68 | `ea03873385e144f54bfb86324ad6785b71d0b02d` | proof/square-root-domain-model | `59d376a668e142b69051ab6cd46bfbff9b30df94` |

Safe proposed order, subject to explicit merge authorization and current-head
qualification: #46 through #68 in order, then resolve and integrate #45 and #44
while preserving their original ancestry and distinct tests/docs. #47–#68 base
SHAs exactly match predecessor heads and are reachable in their respective heads.
Retarget only after the predecessor is reachable from main. Do not squash or
rebase the dependent chain blindly.

Pairwise tree-only merge probes identify content conflicts with the independent
branches. The staged rehearsal resolves these by explicit source union, retaining
#45's byte-identical core once, both independent fixtures, #44's guarded rewrite,
all audit imports/checks, unique Lake registration and original appended receipts.
Source-union verification is separate from construction. No temporary merge
commit or ancestry rewrite is created; validation of this tree does not itself
prove that GitHub can perform the future ordered merges without reviewed
resolution commits. Any changed source head or changed resolved tree requires
requalification.
