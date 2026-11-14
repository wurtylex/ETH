#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
VENDOR="$ROOT/.scratch/wordram-compiler-build"
BUILD="$ROOT/.scratch/wordram-transport-build"
mkdir -p "$BUILD/RAMToTM"
export LEAN_PATH="$BUILD:$VENDOR${LEAN_PATH:+:$LEAN_PATH}"
cd "$ROOT/results/WordRAM"
if rg -n '\bsorry\b|\baxiom\b|native_decide' Transport/*.lean; then
  echo 'Forbidden placeholder or custom proof shortcut in transport sources' >&2
  exit 1
fi
lean -R . -o "$BUILD/RAMToTM/FiniteAddresses.olean" Transport/FiniteAddresses.lean
lean -R . -o "$BUILD/RAMToTM/Table.olean" Transport/Table.lean
lean -R . -o "$BUILD/RAMToTM/TransportCheck.olean" Transport/Axioms.lean > "$ROOT/results/WordRAM/Transport/Axioms.txt" 2>&1
cat "$ROOT/results/WordRAM/Transport/Axioms.txt"
LEAN_PATH="$BUILD:$VENDOR${LEAN_PATH:+:$LEAN_PATH}" lean Transport/TableVerification.lean
