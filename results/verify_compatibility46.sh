#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT/.ultramath/smwg8h0gx/m6"
. tools/leanpath.sh
export LEAN_PATH="$ROOT/.ultramath/smwg8h0gx/m4/lean:$ROOT/.ultramath/smwg8h0gx/m6/lean:$LEAN_PATH"
cd "$ROOT"
lean -o results/Compatibility46.olean results/Compatibility46.lean
