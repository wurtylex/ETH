#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
SRC="$ROOT/results/WordRAM/Pinned"
BUILD="$ROOT/.scratch/wordram-compiler-build"
cd "$SRC"
export LEAN_PATH="$BUILD${LEAN_PATH:+:$LEAN_PATH}"
python3 - "$SRC" "$BUILD" <<'PY'
from pathlib import Path
import re,subprocess,sys,time,hashlib,json
src,build=map(Path,sys.argv[1:])
root='ThreeSumApsp.Lang.Compiler.WholeProgram'
seen=set();queue=[root]
while queue:
    m=queue.pop()
    if m in seen:continue
    seen.add(m)
    for d in re.findall(r'^\s*(?:public\s+)?import\s+([^\s]+)',(src/(m.replace('.','/')+'.lean')).read_text(),re.M):
        if not d.startswith('Mathlib'):queue.append(d)
remaining=set(seen)
# These sources are acyclic; repeatedly compiling the first ready module keeps this script simple.
while remaining:
    ready=None
    for m in sorted(remaining):
        deps={d for d in re.findall(r'^\s*(?:public\s+)?import\s+([^\s]+)',(src/(m.replace('.','/')+'.lean')).read_text(),re.M) if not d.startswith('Mathlib')}
        if deps <= seen-remaining:
            ready=m;break
    if ready is None:raise RuntimeError('import cycle or unavailable local module')
    out=build/(ready.replace('.','/')+'.olean')
    out.parent.mkdir(parents=True,exist_ok=True)
    print('BUILD',ready,flush=True)
    subprocess.run(['lean','-R',str(src),'-o',str(out),str(src/(ready.replace('.','/')+'.lean'))],check=True)
    remaining.remove(ready)
manifest=json.loads((src.parent/'PinManifest.json').read_text())
for item in manifest['files']:
    p=src/item['path']
    assert hashlib.sha256(p.read_bytes()).hexdigest()==item['sha256'],f'modified vendor file: {p}'
print(f'VERIFIED_VENDOR {len(seen)} compiled sources; pinned source hashes unchanged')
PY
# Only the build root belongs on this path: adding the source root can make Lean look for
# freshly-built .olean files next to their sources instead of using the completed build.
LEAN_PATH="$BUILD${LEAN_PATH:+:$LEAN_PATH}" lean "$ROOT/results/WordRAM/CompilerAudit.lean"
