#!/usr/bin/env bash
# Verify the state-size bounds of the Prove2Me RAM -> FinTM2 transport (task C).
# Reuses RAMToTM.Table / RAMToTM.FiniteAddresses built by verify_wordram_simulation.sh.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
VENDOR="$ROOT/.scratch/wordram-compiler-build"
TRANSPORT="$ROOT/.scratch/wordram-transport-build"
FROZEN="$ROOT/.scratch/m7fresh810"
BUILD="$ROOT/.ultramath/smwglrpay/m4/build2"
if [ ! -f "$TRANSPORT/RAMToTM/Table.olean" ]; then
  echo "run ./results/verify_wordram_simulation.sh first (RAMToTM.Table is missing)" >&2
  exit 1
fi
mkdir -p "$BUILD/RAMToTM"
cp "$TRANSPORT"/RAMToTM/*.olean "$BUILD/RAMToTM/"
export LEAN_PATH="$BUILD:$FROZEN:$TRANSPORT:$VENDOR${LEAN_PATH:+:$LEAN_PATH}"
cd "$ROOT/results/WordRAM"
if rg -n '\bsorry\b|\baxiom\b|native_decide|\bdecide\b' Transport/SizeBounds.lean; then
  echo 'Forbidden placeholder or decision shortcut in SizeBounds' >&2
  exit 1
fi
lean -R . -o "$BUILD/RAMToTM/SizeBounds.olean" Transport/SizeBounds.lean
lean -R . Transport/SizeBoundsTest.lean
lean -R . Transport/SizeBoundsAxioms.lean > "$ROOT/results/WordRAM/Transport/SizeBoundsAxioms.txt" 2>&1
cat "$ROOT/results/WordRAM/Transport/SizeBoundsAxioms.txt"
