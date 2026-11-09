#!/usr/bin/env bash
# Local-only validation; requires the pinned Lean/Lake and Python >= 3.11 on PATH.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
lake build
lake env lean Audit.lean
python3 -m unittest discover -s tests -v
