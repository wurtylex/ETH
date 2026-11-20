# ETH proofs — Lean 4.35.0

This is the active Lean project. Its three routes prove the same statement,
`¬ ComplexityAbstracts.SubexponentialSATAbstract.ETH`:

| Route | Endpoint |
| --- | --- |
| OpenAI and its machine-model bridges | `EthBridge.OpenAIChain.not_eth` |
| Anthropic and its machine-model bridge | `EthBridge.AnthropicChain.not_eth` |
| Elementary two-piece core with reused recursion | `EthBridge.Elementary.ReusedRecursion.not_eth` |

The third route is an implementation variant using the existing recursion. It
does **not** certify the exact algorithm in the deconstruction manuscript.
The additional `EthBridge.WordRAM.not_eth_ram` theorem concerns the additive
word-RAM model at logarithmic word size; its precise statement is in
[`EthBridge/WordRAM.lean`](EthBridge/WordRAM.lean). The separate historical
ThreeSumApsp/RAMToTM transport project is not part of this package.

The default Lake targets include all three endpoint modules and WordRAM.
`EthBridge/Shared/` contains reusable lemmas consumed by the proof routes.
`AnthropicEth/` and `OpenAIEth/` retain the upstream module structure and
attribution; `vendor/` contains the adapted complexitylib and cslib sources.
[`lake-manifest.json`](lake-manifest.json) fixes all dependency revisions,
including Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` for Lean 4.35.0.
The optional upstream documentation projects requiring 4.36 tools were omitted.

## Verification runs on a remote machine

Do not run Lean, Lake, or elan on this computer. The launcher below only
packages files, uses SSH, and checks returned hashes locally. Lean commands
run on the selected remote server. A new checkout needs Python 3 and SSH
locally; the remote server needs Python 3, Git, and the exact
`leanprover/lean4:v4.35.0` toolchain already installed with elan.

From the repository root:

```bash
python3 lean/scripts/verify_remote.py \
  --host USER@SERVER --port SSH_PORT \
  --remote-root /REMOTE/NEW-EMPTY-WORKSPACE
```

The destination must not already exist. An optional `--cache-project` argument
reuses an existing 4.35 project's artifacts by copying them into the isolated
workspace; historical sources and evidence are left untouched. Use
`--known-hosts PATH` for a dedicated, already trusted SSH known-hosts file.
Without a cache, Lake resolves the committed manifest and builds dependencies
on the remote machine. This can take substantial time and disk space.

The launcher checks the default build, exact endpoint applications, the C1
WordRAM application, 194 axiom closures, and 106 normalized compiled declaration
types against the saved 4.35 baseline. Only `propext`, `Classical.choice`, and
`Quot.sound` are allowed by the axiom audit. It checks source hashes before and
after execution and again after retrieving evidence. Results are written to
[`audit/verification/`](audit/verification/); no prior `results/Audit/` checkout
is required. The internal worker refuses execution outside an SSH session.

These checks cover the endpoint import closures and the listed declarations.
They do not claim to build every optional test, unrelated upstream library
module, or documentation generator in the vendored libraries.

## Provenance and negative controls

[`audit/source-provenance.json`](audit/source-provenance.json) records the
verified source snapshot, the relocation, and intentional omissions.
[`audit/source-inventory.json`](audit/source-inventory.json) maps retained
source paths to their original SHA-256 hashes. All 10,153 retained mathematical
Lean files are byte-identical to that snapshot. Only the root README and Lake
configuration changed during the relocation; the audit files are separate.
The normalized baseline and audit probes are included in `audit/`.

`Planted/` contains deliberately invalid negative fixtures, including admitted
proofs, extra axioms, and incorrect statements. They are excluded from the
default targets and from every verified proof. They must not be presented as
formal results or imported into an endpoint.

This project is licensed under the [Apache License, Version 2.0](LICENSE).
The imported Anthropic/OpenAI,
complexitylib, and cslib trees retain their own Apache-2.0 licenses and notices.
Those licenses and the source attribution remain applicable to their files.
