# Dependency and source provenance

John Funge licenses the migrated original project sources under the MIT
license in LICENSE. The source originated in private relgraph; this decision
does not change relgraph's license or the licenses of dependencies. All 77 commits touching the two Lean
paths through the baseline identify John Funge; pending #74 does too. See the
[source mapping](provenance/source-map.json). This is a practical provenance check,
not a legal opinion or claim that Git authorship alone proves ownership.

No C library files, thesis/paper PDFs, Markdown transcriptions, or private source
inventories are copied. Proofs reference their mathematical sources. The formal
files contain no third-party copyright/SPDX headers identified by this inspection;
imports from mathlib are dependencies, not vendored source. The source tree's
`hardware/adapter.c` is the Lean demo FFI support already developed in the
formalization directory; it is distinct from relgraph/src and migrates with Lean.
Its native/compiler/IEEE trust boundary is unchanged.

Lean 4.19.0 is Apache-2.0 (the installed distribution also contains a LICENSES
file for bundled third-party components). Mathlib and Lake dependencies remain
external, pinned in lake-manifest.json, and retain their own licenses. Existing
cloud caches are used only for validation and are excluded from Git and export.

| Package | Pinned revision | License inspected in cache | Upstream |
| --- | --- | --- | --- |
| mathlib | `c44e0c8ee63ca166450922a373c7409c5d26b00b` | Apache-2.0 | [license](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/LICENSE) |
| plausible | `77e08eddc486491d7b9e470926b3dbe50319451a` | Apache-2.0 | [license](https://github.com/leanprover-community/plausible/blob/77e08eddc486491d7b9e470926b3dbe50319451a/LICENSE) |
| LeanSearchClient | `25078369972d295301f5a1e53c3e5850cf6d9d4c` | Apache-2.0 | [license](https://github.com/leanprover-community/LeanSearchClient/blob/25078369972d295301f5a1e53c3e5850cf6d9d4c/LICENSE) |
| importGraph | `e6a9f0f5ee3ccf7443a0070f92b62f8db12ae82b` | Apache-2.0 | [license](https://github.com/leanprover-community/import-graph/blob/e6a9f0f5ee3ccf7443a0070f92b62f8db12ae82b/LICENSE) |
| proofwidgets | `c4919189477c3221e6a204008998b0d724f49904` | Apache-2.0 | [license](https://github.com/leanprover-community/ProofWidgets4/blob/c4919189477c3221e6a204008998b0d724f49904/LICENSE) |
| aesop | `5d50b08dedd7d69b3d9b3176e0d58a23af228884` | Apache-2.0 | [license](https://github.com/leanprover-community/aesop/blob/5d50b08dedd7d69b3d9b3176e0d58a23af228884/LICENSE) |
| Qq | `fa4f7f15d97591a9cf3aa7724ba371c7fc6dda02` | Apache-2.0 | [license](https://github.com/leanprover-community/quote4/blob/fa4f7f15d97591a9cf3aa7724ba371c7fc6dda02/LICENSE) |
| batteries | `f5d04a9c4973d401c8c92500711518f7c656f034` | Apache-2.0 | [license](https://github.com/leanprover-community/batteries/blob/f5d04a9c4973d401c8c92500711518f7c656f034/LICENSE) |
| Cli | `02dbd02bc00ec4916e99b04b2245b30200e200d0` | MIT | [license](https://github.com/leanprover/lean4-cli/blob/02dbd02bc00ec4916e99b04b2245b30200e200d0/LICENSE) |

No dependency is being relicensed or copied into this migration. Publishing the
project's own sources under MIT would not change dependency license obligations.
