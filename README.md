# ETH formalization work

This repository contains the Lean sources, pinned definitions, verification
reports, source provenance and portable source archives from the **here are two
papers** work session. No unpublished dependency or compiled cache is included
in the repository.

## Start here

- [Verification scope and provenance](results/EthBridgeVerification.md)
- [Download and local setup](results/DOWNLOADING.md)
- [Reproduce the current bridge checks](results/verify_eth_bridges.sh)
- [Complete source-and-results archive](results/Downloads/eth-work-source-and-results.zip)

## Current checked results

The current Lean **4.36.0-rc2** aggregate build includes both bridges. The exact
checked results and axiom reports are in the verification files:

1. **C1** — `EthBridge.WordRAM.not_eth_ram` proves `¬ ETH_RAM` for the stated
   fixed additive word-RAM model, including its specified logarithmic-width and
   input-fit contract. This is not an unqualified claim about every informal
   notion of an “ordinary algorithm.”
2. **C2** — `EthBridge.Anthropic.not_eth_of_ethIsFalse` proves
   `MainResults.ETHIsFalse → ¬ ComplexityAbstracts.SubexponentialSATAbstract.ETH`.
   **The premise remains a premise.** The checked transport is not a new
   unconditional proof of Anthropic's hypothesis.
3. Complexitylib's existing `not_eth` independently checks with only the usual
   foundational axioms: `propext`, `Classical.choice` and `Quot.sound`.

See [the exact verification output](results/EthBridgeVerification.txt). Cert-
machine acceptance has not been run for the current bridges. A successful local
Lean build is not by itself a paper-level model review.

## Repository layout

- `results/ClaimboxC2Build/`: editable Lean package for the C1/C2 bridges,
  exact pinned dependency manifest, and focused Lean check files.
- `results/Vendor/ClaimboxC2/`: vendored source snapshot, pin manifest and
  upstream MIT license.
- `results/WordRAM/`: other pinned machine sources, authored transport code and
  historical verification records. These are **not all ordinary word-RAM proofs
  of ETH**; read the individual READMEs and scope notes.
- `results/Downloads/`: source archives. The complete archive includes the
  original `formal-math-main` snapshot, with its ETH paper, full Lean 4.33.1
  proof tree and Apache license/notice.
- Build and verification logs: evidence of the particular commands run, with
  retained warnings and failures. They are not blanket certification.

`results/verify_eth_bridges.sh` is the intended portable post-setup check for
the current bridges. **Other older scripts are records, not automatic setup
recipes:** some refer to VM-local `.ultramath/` or `.scratch/` exploratory
workspaces, which are excluded here. Some intermediate verification programs
and environments are therefore not available after cloning; their retained
logs are not promises of reproduction from this repository. The complete
source archive does include the original `formal-math-main` ETH project as
described in the download guide. Committing new dependencies or updating
toolchain pins should be an explicit, reviewed change.

## What's deliberately not tracked

`.lake/`, `.scratch/`, `.ultramath/`, `.skill/`, `.olean` files and other build/
tool caches remain ignored. The VM's dependency cache is about 16 GB and should
not be pushed. Do not run `lake update` during initial setup; dependencies are
pinned by the manifests.

Third-party code has different licenses. The relevant MIT and Apache license
files/notices are retained with the vendor and archived source material. No
extra license is asserted here for new material.
