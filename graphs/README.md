# ETH dependency graphs

This package recreates the two saved **Lean 4.35.0** graph websites using Python 3.10+ and no additional packages. It includes the frozen compiled-reference snapshots and saved coordinates; building the website does **not** execute Lean, recheck the proofs, or rerun clustering.

From the repository root:

```sh
python3 graphs/build.py
python3 graphs/serve.py
```

Open <http://127.0.0.1:8768/>. The site contains the interactive graphs, full JSON downloads, PNG previews, method notes and a ZIP for slides. Use `--port 8769` if another graph server already occupies the default port. Generated files go into ignored `graphs/dist/`; runtime files stay outside the public site.

| View | Declarations | Directed references | Communities |
|---|---:|---:|---:|
| All three routes | 61,514 | 453,353 | 72 |
| Anthropic + our route | 15,111 | 95,461 | 37 |

The reduced view removes exactly the OpenAI-only declarations and clusters the remaining induced graph afresh. It retains 5,358 declarations shared by Anthropic and our route. These all appear purple there; 2,433 also occur in OpenAI's proof. The full view keeps seven exact membership colors. Original three-route membership fields remain in both JSONs.

Nodes include definitions and generated helpers as well as theorems. Edges are direct compiled references. Full reachability is computed before excluding common foundation modules; the displayed graphs add no shortcut edges. Colors show endpoint reachability, while clusters follow dependency connections. Cluster labels summarize module families after grouping. Screen distances are presentation choices, not mathematical distances or proof complexity measurements.

The default overview draws a fixed 10% sample of connections at 3.5% opacity. Clustering and downloads retain every edge. Selecting a node reveals its direct connections within active filters. The two line controls, ancestry and community filters, search, **Show cluster names**, PNG export and navigation are preserved from the checked public snapshot.

## Proof scope and provenance

The three source endpoints are `EthBridge.OpenAIChain.not_eth`, `EthBridge.AnthropicChain.not_eth` and `EthBridge.Elementary.ReusedRecursion.not_eth`. The third uses a two-piece core with Anthropic's existing recursion. It is an implementation variant; formalization of the manuscript's exact algorithm remains separate work.

`snapshots/manifest.json` pins every input, the original public asset hashes and source evidence hashes. `snapshots/graph-summary.json` records the roots, compiler version, palettes, counts and provenance. The builder checks compressed inputs, reconstructs the original graph JSON and HTML byte-for-byte, and validates all public links. The ZIP's member payloads are fixed; its compressed container bytes may depend on Python/zlib. Historical evidence hashes identify the source run and do not imply that a fresh clone independently repeats that verification. Canonical Lean sources and verification instructions live in the repository's `lean/` directory.

The saved HTML templates include the renderer, styles and UI code. Only graph data is injected during the build. Neither historical audit directories nor remote server details are needed to build or serve this package. `layout/` preserves the separate clustering algorithm and its original versions for optional experimentation; it is unnecessary for viewing and is never invoked by the build.

Check the snapshot and publication boundary with:

```sh
python3 graphs/check.py
```

## Temporary public sharing

The local viewer is portable. The detached sharing manager uses Linux `/proc` to verify ownership of its processes, and requires `cloudflared` on `PATH`. No account key is needed for a temporary tunnel.

```sh
python3 graphs/host.py status
python3 graphs/host.py share
python3 graphs/host.py stop
```

`share` builds no files; run `build.py` first on a fresh clone. It starts the loopback-only origin and a Cloudflare quick tunnel, then prints the URL. Keep this computer awake and connected. Restarting the tunnel changes that URL. Only the eleven named public assets are served; source files, manifests, logs, credentials and directories are excluded.

For an existing tunnel, `share` reuses its running origin and URL. To adopt a newly built bundle while preserving the running tunnel:

```sh
python3 graphs/build.py
python3 graphs/host.py refresh
```

`refresh` validates the new bundle, replaces only this task's origin server and keeps the tunnel process running. There may be a brief interruption. The manager also recognizes the original pre-cleanup server's literal command path, even when the old audit directory has been archived. It does not depend on that directory on a fresh clone. Building or checking this package never changes the old live publication tree in `.scratch/public-graphs/`.

Some text-only browsing tools cannot fetch temporary tunnel domains or execute the canvas viewer. Give them the landing page's slide PNGs and method notes, or attach `slide-assets.zip` from a browser.
