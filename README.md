# ETH formalizations

Lean formalizations of the OpenAI and Anthropic ETH arguments, shared lemmas,
and an elementary two-piece route using Anthropic's generic recursion.
The active Lean workspace uses **Lean 4.35.0** and Mathlib **v4.35.0**.

| Directory | Contents |
| --- | --- |
| [lean/](lean/README.md) | Formal sources, pinned dependencies, licenses and remote verification tools |
| [lean/audit/](lean/audit/) | Source provenance, axiom/type checks and verification evidence |
| [graphs/](graphs/README.md) | Interactive graph builders, compressed snapshots, slide images and hosting tools |

## Formal statements and scope

The three endpoints prove the same project statement,
`¬ ComplexityAbstracts.SubexponentialSATAbstract.ETH`:

| Route | Declaration |
| --- | --- |
| OpenAI | `EthBridge.OpenAIChain.not_eth` |
| Anthropic | `EthBridge.AnthropicChain.not_eth` |
| Elementary two-piece route | `EthBridge.Elementary.ReusedRecursion.not_eth` |

The third route is an **implementation variant** using the new two-piece core
with existing recursion. Formalizing the manuscript's exact algorithm remains
separate work. The WordRAM bridge is also a default build target. Intentionally
invalid `Planted/` fixtures are separate from the verified proof targets.

See [the Lean project](lean/README.md) for exact targets, dependency pins,
verification results and reproducible commands. Run Lean, Lake and elan on an
authorized remote machine; no Lean compilation is performed on this workstation.

## Dependency graphs

The [graph package](graphs/README.md) rebuilds both interactive pages from saved
Lean 4.35 compiled-reference snapshots, using Python without running Lean.
It includes zoom, declaration search, cluster selection, line controls, a
**Show cluster names** switch, and PNG export.
Both views unify the final proof declarations into one displayed **¬ETH**
conclusion and offer **Find ETH**. Each route's proof remains inspectable.
The reduced view also has a source-linked **Compare proof steps** guide showing
our constructions, Anthropic counterparts, and exact reuse points.

| Setup | Declarations | Direct references | Clusters |
| --- | ---: | ---: | ---: |
| All three routes | 61,514 | 453,353 | 72 |
| Anthropic + our route | 15,111 | 95,461 | 37 |

The reduced view removes OpenAI-only declarations. Its purple category combines
all **5,358 declarations shared by Anthropic and our route**, including those also
used by OpenAI. The full view retains seven exact membership colors.

Clusters follow dependency structure. Screen distance is presentation geometry,
not a mathematical similarity measure. A graph rebuild renders the saved
snapshot; it is not a new Lean verification or dependency extraction.

[Temporary public graph pages and slide assets](https://sms-model-pond-landscapes.trycloudflare.com/)
are served from this computer. The link requires the computer and tunnel to stay
online. Portable build, hosting and slide-download instructions are in
[graphs/README.md](graphs/README.md).

## Historical material and licenses

Earlier workspaces, audit runs, experimental WordRAM compiler/transport projects,
and generated artifacts are retained in an ignored local archive. They are not
part of the active 4.35 workspace. The initial committed sources remain available
in Git history at `58736fc`; the standalone historical WordRAM experiments are
not represented as verified 4.35 code.

Upstream port notes may mention older toolchain versions as historical provenance;
the active workspace and all retained toolchain files are pinned to 4.35.0.

Upstream licenses and notices remain beside their sources, including the original
Claimbox MIT license in [lean/LICENSE](lean/LICENSE) and the OpenAI, Anthropic,
complexitylib and cslib license/notice files. Provenance distinguishes original
sources, compatibility changes and shared refactorings.
