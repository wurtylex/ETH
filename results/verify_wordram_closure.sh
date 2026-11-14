#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
SRC="$ROOT/results/WordRAM/Transport"
BUILD="$ROOT/.scratch/wordram-closure-build"
UPSTREAM="$ROOT/.ultramath/smwgnm7hp/m2/build"
FROZEN="$ROOT/.scratch/m7fresh810"
PINNED="$ROOT/.scratch/wordram-compiler-build"
VENDOR="$ROOT/.scratch/wordram-transport-build"
mkdir -p "$BUILD/RAMToTM/Transport"
cp -r "$UPSTREAM/RAMToTM/." "$BUILD/RAMToTM/"
export LEAN_PATH="$BUILD:$FROZEN:$VENDOR:$PINNED${LEAN_PATH:+:$LEAN_PATH}"
for f in InitPoly InitPrims StepPoly Closure; do
  cmp "$SRC/RAMToTM/Transport/$f.lean" \
      "$ROOT/.ultramath/smwgnm7hp/m2/src/RAMToTM/Transport/$f.lean"
done
if rg -n '\bsorry\b|\badmit\b|\baxiom\b|native_decide' "$SRC/RAMToTM/Transport"/*.lean; then
  echo 'Forbidden placeholder or proof shortcut in closure source' >&2
  exit 1
fi
cd "$SRC"
for M in StepPoly InitPrims InitPoly Closure; do
  lean -R . -o "$BUILD/RAMToTM/Transport/$M.olean" \
      "RAMToTM/Transport/$M.lean" > "$ROOT/results/WordRAM/Transport/$M.build.log" 2>&1
  grep -E 'depends on axioms|does not depend' \
      "$ROOT/results/WordRAM/Transport/$M.build.log" || true
done
cat > "$BUILD/ClosureSignatures.lean" <<'EOT'
import RAMToTM.Transport.Closure
#check @RAMToTM.Transport.nonempty_isPolyT_machine
#check @RAMToTM.Transport.exists_tmW_of_exec_unconditional
#print axioms RAMToTM.Transport.exists_tmW_of_exec_unconditional
#print axioms CountKSat.exists_tmW
EOT
lean -R . "$BUILD/ClosureSignatures.lean" > "$ROOT/results/WordRAM/Transport/ClosureSignatures.txt" 2>&1
cat "$ROOT/results/WordRAM/Transport/ClosureSignatures.txt"
sha256sum "$ROOT/.ultramath/smwg2471j/m4/eth/MainResults.lean"
