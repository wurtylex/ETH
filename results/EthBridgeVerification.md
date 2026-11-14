# EthBridge: local verification and scope

## Checked outcomes

The current `EthBridge.lean` imports both bridges and the aggregate `lake build`
succeeds using **Lean 4.36.0-rc2**. The focused checks apply the exact exported
theorems to their declared types:

- **C2:** `EthBridge.Anthropic.not_eth_of_ethIsFalse` proves
  `MainResults.ETHIsFalse → ¬ ComplexityAbstracts.SubexponentialSATAbstract.ETH`.
  This transports **the hypothesis** about Anthropic's duplicate-free `FinTM2`
  formulation to complexitylib's deterministic multitape formulation. Its target
  uses `encCNF`, `CNF.numVars`, and clauses of at most three literals.
- **C1:** `EthBridge.WordRAM.not_eth_ram` proves the negation of its own
  `ETH_RAM`. Its definition requires one fixed additive-basis word-RAM program,
  deciding 3-SAT on `encCNF` bits stored one bit per word, at widths above the
  specified positive multiple of logarithmic input length, subject to the
  machine model's input-fit contract. This is an unconditional theorem about
  that formal model, not a new unrestricted claim about every implementation of
  an “ordinary algorithm.”
- complexitylib's existing `SubexponentialSATAbstract.not_eth` also checks, with
  no additional hypothesis. C2 supplies a transport of Anthropic's proposition;
  it is not needed to make complexitylib's existing `not_eth` unconditional.

For C1, the checks additionally include `executes_simProgram_of_space`,
`uniformDecidable_of_timeSpace`, and `exists_ksat3_decider`. Each checked theorem,
as well as C2 and complexitylib's `not_eth`, reports exactly:

```text
[propext, Classical.choice, Quot.sound]
```

There is no `sorryAx` or added proposition-specific axiom in these theorem
closures. That is a proof-status result, not by itself evidence of fidelity to a
paper's intended mathematics.

## Provenance

- Anthropic `eth/MainResults.lean`: commit
  `16a5ce41304fcdaea4e0be7c132e1c361dc26da5`, SHA-256
  `47f78a9550d95b37d8718dd1ee16ae824da893a5e17c319f737e6d0a5ed24944`.
  A direct download from that commit compares byte-for-byte with the imported
  local statement file. It is elaborated here with the newer Lean and Mathlib;
  this check is not a compilation of an old 4.33 `.olean` under 4.36.
- complexitylib: `7c66eb718fb2c1ea8d5037bc0bbee64912cfc030`.
- CSLib: `254e30e6d4299c51323aaeaf5f51a4763b375d4a`.
- Mathlib: `69552756cd8a2d2d48763cf7279fd814d6a1224d`.

All 24 files claimed by `Vendor/ClaimboxC2/PIN.json` are present with their exact
sizes and hashes, and the files in `ClaimboxC2Build` match them. The three named
dependency revisions match and have clean Git worktrees. `Planted/` contains
intentionally incorrect examples and is not part of this build.

## Reproduction

From the project root, run:

```bash
bash results/verify_eth_bridges.sh
```

The script selects an explicitly supplied `ELAN_HOME`, otherwise the VM's local
`.scratch/elan` when present, otherwise the usual `$HOME/.elan`. It preserves
cached dependencies and does not update source pins or manifests. In this VM,
the system-provided `lake env lean` would otherwise select Lean 4.33.1 and is not
the compiler for these artifacts. The script expects an already installed
4.36.0-rc2 toolchain; it does not download one.

This is a **local Lean kernel check**, not the repository's independent
`cert-machine` acceptance process and not an independent paper-level review of
the word-RAM or Turing-machine models. This run did not recheck the original
Anthropic proof of `MainResults.ETHIsFalse`, which is a separate artifact in its
own toolchain. C2's check here establishes the stated implication; accepting its
hypothesis requires that separate original-toolchain evidence and a documented
cross-version correspondence.
