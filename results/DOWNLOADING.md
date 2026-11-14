# Downloading and continuing this work

Two ZIP exports are available in `results/Downloads/`:

- `eth-work-source-and-results.zip`: the complete source-and-results export. It
  contains all source files, pinned vendors, authored transport files, notes,
  and result logs under `results/`, plus the original `formal-math-main/`
  source snapshot used by the earlier proof checks, including the ETH paper and
  its complete Lean proof project.
- `eth-bridge-only.zip`: only the current C1/C2 EthBridge project, its exact
  pinned vendor copy and pin manifest, focused Lean checks, verification script,
  and verification report.

Both omit compiled `.olean` files, `.lake/` dependency and build trees, VM-local
toolchain downloads, and other regenerable cache output. They do not include a
virtual machine. A `MANIFEST.sha256` inside each ZIP lists hashes of its files.
`results/Downloads/SHA256SUMS.txt` covers the downloaded ZIPs themselves.

## Prerequisites and setup for the current bridge

You need Git, a C compiler toolchain, and [elan](https://github.com/leanprover/elan),
Lean's version manager. The project's `lean-toolchain` automatically selects
**leanprover/lean4:v4.36.0-rc2**. If you need elan on Linux or macOS, its official
installation command is:

```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
```

Follow its PATH setup prompts, or restart the shell afterwards. This changes
your local development environment; it is not necessary if elan is already
installed. The authoritatively documented installation is at
<https://github.com/leanprover/elan#installation>.

After extracting either archive, enter its root directory and run:

```bash
cd results/ClaimboxC2Build
lake env lean --version
lake exe cache get
lake build
lake env lean Check.lean
lake env lean CheckC1.lean
cd ../..
bash results/verify_eth_bridges.sh
```

`lake env lean --version` should report Lean **4.36.0-rc2**. Lake fetches the
revisions in the included `lake-manifest.json`; `lake exe cache get` downloads
available prebuilt Mathlib artifacts so you do not need to rebuild all of
Mathlib. These commands require network access and enough disk space for the
cache. Do not run `lake update` as part of this setup: the dependency commits
are intentionally pinned.

The verifier accepts an already set `ELAN_HOME`, otherwise it uses
`.scratch/elan` if present or the usual `$HOME/.elan`. It creates only its local
temporary directory, build caches, and the verification log. Dependency
checkouts are pristine on import, and source files match the included pins.
Editing a pinned source will make the provenance comparison fail until you
intentionally update its pin record; ordinary `lake build` and the focused Lean
checks remain available while developing.

## Original Anthropic ETH project (main archive only)

To work on the original proof, enter:

```bash
cd formal-math-main/eth
```

Then follow that directory's own `README.md`. In particular:

```bash
lake exe cache get
lake build
lake env lean scripts/PrintAxioms.lean
```

This is a separate **Lean 4.33.1** project with its own included Lake manifest.
Its two intentional `sorry` warnings from `Challenge.lean` are separately
explained in its README; that statement file is not a proof. The complete
`formal-math-main` source snapshot has the Apache license and source notices.
Its provenance in this export is "the snapshot used by the earlier work"; its
Git metadata was not present in the working copy and therefore is not claimed
to be a Git checkout.

## Scope

No external cert-machine certification was run for the current bridges. A local
successful build is not an independent model review; see
`results/EthBridgeVerification.md`. The build script for the current bridge is
intended to work after the setup above. Other older scripts under `results/`
are retained for provenance and may point at VM-specific exploratory workspaces;
their needed sources are included where present, but their transient build
outputs and VM tool paths are not a portable environment. No third-party
compiled dependencies are claimed to be redistributed inside the bundles.

The Open Math OS project is not connected to GitHub. These ZIPs are therefore
the direct way to take the sources elsewhere without pushing anything to an
external repository.
