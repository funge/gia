# Local standalone migration preparation

John Funge has applied MIT licensing to the migrated original sources,
preserving gia's existing MIT LICENSE and initial commit
`5205f7794e34d6841b7bd3bd6e9898caaf743ab1`. The earlier local preparation retained
the source license until this owner action. Relgraph and dependency licenses
are unchanged. The steps below record the preparation and handoff; historical
AGPL references describe provenance, not gia's current license.

## Baseline and pending review

The baseline is relgraph main `7fd4b39dc127dec3be1b96a46cf392d4bcd73d2b`:
156 files relocated from formalization/lean to this repository root. Earlier
formalization/lean-pilot history is recorded too. The [source map](provenance/source-map.json)
records every original path/blob/mode plus 77 path-history commit IDs and author
records, without importing any unrelated private repository history. Original
source commits remain in private relgraph; mapping is provenance, not rewritten
original Git ancestry. Historical validation paths remain labeled as history.

Square-root PR #74 (`f7cfea863529e48dffddc393cb9fb25d41ea9b03`) is excluded from
the baseline and prepared on a separate local pending branch/patch. It has not
been merged or closed. Migration changes import no proof assumptions, change no
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

## Recorded owner handoff and remaining review steps

1. Review the baseline snapshot, provenance, validation receipt, and separate #74
   patch. Decide/apply the final license for John's migrated sources in the public
   gia checkout; this preparation intentionally retains the old license.
2. Copy the baseline tracked source files into the existing gia checkout, preserving
   its initial history and John-approved LICENSE. Do not copy .git, .lake, caches,
   private relgraph history or Tupper source documents. Resolve the preparation
   notice and record the licensing decision, then run both checks and publish.
3. Apply the pending #74 patch as a separate gia review branch, retaining its source
   commit reference. Review it separately; only then coordinate the disposition
   of relgraph PR #74. This preparation does neither action.
4. Once the public baseline is available, review/publish the separate relgraph
   removal commit: only Lean-owned files are removed and README gains a related
   gia link. All other tracked blobs/modes, including C/library/build inputs, must
   match the original baseline. There is no relgraph dependency on gia.

The sibling migration validation receipt records exact prepared commits and results.
