# Optional fresh layout

`community_layout.py` is the unchanged algorithm that produced the saved Lean 4.35 graphs. Its SHA-256 and tool versions are recorded in `versions.json`. The website build uses saved coordinates and does not import this module.

For experiments, install the Python packages listed in `requirements.txt` into a separate environment, and install Graphviz 16.1.1 (`neato` and `sfdp` on `PATH`). Then call `community_layout.layout(graph['nodes'], graph['edges'])` on either decompressed snapshot. The returned layout is separate from the saved website; it does not rewrite the snapshot.

Leiden RBConfiguration uses sorted declaration identities, deduplicated undirected non-self dependency links, resolution 1 and seed 42. Membership colors, module labels and previous coordinates are excluded from grouping. Graphviz packs communities and lays out each community internally. Names summarize communities only afterward.

Saved positions are exact snapshots. Recomputing geometry is not promised to be bit-identical: a prior full-graph permutation check found identical community memberships but small floating-coordinate differences. Changing dependencies, names or library versions can also change clustering. Community IDs are local to each graph, and screen distance is not mathematical distance.
