#!/usr/bin/env bash
# No Lean installation required. Tests the same object linked into the Lean FFI.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
if [[ $# == 0 ]]; then
  out="$(mktemp -d)"
  trap 'rm -rf "$out"' EXIT
elif [[ $# == 1 ]]; then
  mkdir "$1" # Refuse to overwrite any prior evidence.
  out="$(cd "$1" && pwd)"
else
  echo "Usage: $0 [new-output-directory]" >&2
  exit 2
fi
bash hardware/build_core.sh "$out"
