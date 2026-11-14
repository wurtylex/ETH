#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BUILD="$ROOT/results/ClaimboxC2Build"
VENDOR="$ROOT/results/Vendor/ClaimboxC2"
if [ -z "${ELAN_HOME:-}" ]; then
  if [ -d "$ROOT/.scratch/elan" ]; then
    export ELAN_HOME="$ROOT/.scratch/elan"
  else
    export ELAN_HOME="$HOME/.elan"
  fi
fi
export PATH="$ELAN_HOME/bin:$PATH"
export TMPDIR="$ROOT/.scratch/lake36-tmp"
mkdir -p "$TMPDIR"
if ! command -v lake >/dev/null || ! command -v lean >/dev/null; then
  echo "The project-local Lean 4.36.0-rc2 toolchain is missing: $ELAN_HOME" >&2
  exit 1
fi
{
  echo '== Toolchain =='
  lake --version
  lake env lean --version
  lake env lean --version | grep -F '4.36.0-rc2' >/dev/null
  echo '== Exact source pins =='
  python3 - "$ROOT" <<'PY'
import hashlib
import json
from pathlib import Path
import subprocess
import sys
root = Path(sys.argv[1])
vendor = root / "results/Vendor/ClaimboxC2"
build = root / "results/ClaimboxC2Build"
pin = json.loads((vendor / "PIN.json").read_text())
for item in pin["files"]:
    path = vendor / item["path"]
    data = path.read_bytes()
    assert len(data) == item["bytes"], f"size mismatch: {path}"
    assert hashlib.sha256(data).hexdigest() == item["sha256"], f"hash mismatch: {path}"
    assert data == (build / item["path"]).read_bytes(), f"build differs: {item['path']}"
print(f"PASS: all {len(pin['files'])} pinned source files are exact")
for package, rev in [
    ("complexitylib", "7c66eb718fb2c1ea8d5037bc0bbee64912cfc030"),
    ("cslib", "254e30e6d4299c51323aaeaf5f51a4763b375d4a"),
    ("mathlib", "69552756cd8a2d2d48763cf7279fd814d6a1224d"),
]:
    git = ["git", "-C", str(build / ".lake/packages" / package)]
    actual = subprocess.check_output(git + ["rev-parse", "HEAD"], text=True).strip()
    assert actual == rev, f"wrong {package} revision: {actual}"
    assert not subprocess.check_output(git + ["status", "--short"], text=True).strip(), \
        f"modified dependency: {package}"
    print(f"PASS: {package} {rev}, no local modifications")
PY
  echo '== Aggregate build; Planted is not a default target =='
  cd "$BUILD"
  env -u LEAN_PATH lake build
  echo '== C2 and its exact application =='
  env -u LEAN_PATH lake env lean Check.lean
  echo '== C1 and its exact application =='
  env -u LEAN_PATH lake env lean CheckC1.lean
  echo "All EthBridge checks passed. No source or manifest was updated."
} 2>&1 | tee "$ROOT/results/EthBridgeVerification.txt"
