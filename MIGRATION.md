# Standalone migration provenance

John Funge has applied MIT licensing to the migrated original sources,
preserving gia's existing MIT LICENSE and initial commit
`5205f7794e34d6841b7bd3bd6e9898caaf743ab1`. The earlier local preparation retained
the source license until this owner action. Relgraph and dependency licenses
are unchanged. The steps below record the preparation and handoff; historical
AGPL references describe provenance, not gia's current license.

## Published baseline and separate square-root review

The baseline is relgraph main `7fd4b39dc127dec3be1b96a46cf392d4bcd73d2b`:
156 files relocated from formalization/lean to this repository root. Earlier
formalization/lean-pilot history is recorded too. The [source map](provenance/source-map.json)
records every original path/blob/mode plus 77 path-history commit IDs and author
records, without importing any unrelated private repository history. Original
source commits remain in private relgraph; mapping is provenance, not rewritten
original Git ancestry. Historical validation paths remain labeled as history.

The published gia baseline is `1f67388d6e11a3eb3677900fd9826899433935e1`,
whose sole parent is the existing MIT initial commit. Its tree matches the local
preparation except for the five expected owner-applied license/documentation files.
Square-root source PR #74 (`f7cfea863529e48dffddc393cb9fb25d41ea9b03`) remains
open and unmerged in relgraph. This separate gia review carries its proof/runtime
changes without altering the published MIT license or copyright notice. Migration changes import no proof assumptions, change no
mathematical theorem, and keep pinned Lean/mathlib versions.

## Standalone checks

From this repository root, with Lean 4.19.0 on PATH:

```sh
./check.sh
./hardware/check.sh
# Optional, explicit access to a matching relgraph source checkout:
RELGRAPH_CHECKOUT=/path/to/relgraph python3 -m unittest discover -s tests -p test_operation_coverage.py -v
```

Default validation reads only [the pinned symbol inventory](provenance/relgraph-api.json):
58 symbols across four public headers at the baseline commit, with Git blob IDs
and SHA-256 hashes. It contains names/provenance, not header or C implementation
copies. The optional comparison detects missing/extra headers, byte changes and
symbol drift; it never clones or discovers sibling checkouts. A changed C API
requires an explicit inventory/ledger update, not silent validation against a
random nearby repository.

A fresh checkout needs the ordinary public Lean/mathlib dependencies. No private
relgraph or graphing access is required to build. Pinned implementation links to
relgraph may require access; they are reference evidence only. Original public
thesis/paper citations replace private graphing links; no source documents are
bundled. See [dependency provenance](THIRD_PARTY.md). Local cloud cache symlinks
used for testing are ignored and must not be published.

## Completed owner handoff and remaining review

John completed the MIT licensing decision and published the baseline. The earlier
private preparation and its AGPL license were historical staging artifacts, not
this project's current license. No further license change is part of square root.

The separate square-root review preserves the original source commit and existing
proof assumptions. The relgraph removal/README update is a different review and
must preserve all retained C/library/build files byte-for-byte. Neither review
implicitly merges or closes original relgraph PR #74. No relgraph dependency on
gia is introduced.

Fresh qualification for the published layout is recorded in [VALIDATION.md](VALIDATION.md).
The local migration receipt and old paths describe the earlier preparation;
they are not required files or build inputs for this repository.
