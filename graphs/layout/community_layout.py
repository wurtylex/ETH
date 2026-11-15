"""Dependency communities and a reproducible packed galaxy presentation.

Leiden sees only sorted declaration names and deduplicated undirected dependency
links. Names supply canonical indices and IDs, not semantic features. Colors,
module names, previous coordinates and edge payloads are ignored. Community IDs
are zero-based in order of each community's smallest full declaration name.

Graphviz neato packs community circles, weighted by actual cross-community link
counts. Independent sfdp layouts place each community's induced graph inside its
circle. Aggregate links are layout inputs only, never replacement proof edges.
Geometry is a presentation of inferred structural communities, not mathematical
distance. Reproducibility assumes the same graph, names, seed and tool versions.
"""

from collections import Counter
from collections.abc import Mapping
from concurrent.futures import ThreadPoolExecutor
from functools import lru_cache
import importlib.metadata
import math
import shutil
import subprocess

import igraph
import leidenalg

ALGORITHM_VERSION = "leiden-rb-neato-sfdp-galaxy-v1"
SEED = 42
RESOLUTION = 1.0
MAX_WORKERS = 4
PACKING_FACTOR = 1.08
LOCAL_DISK_FACTOR = 0.90


def _canonical_graph(nodes, edges):
    names = []
    seen = set()
    for i, node in enumerate(nodes):
        if not isinstance(node, Mapping) or not isinstance(node.get("name"), str) or not node["name"]:
            raise ValueError(f"Node {i} must have a nonempty string name")
        if node["name"] in seen:
            raise ValueError(f"Duplicate declaration name: {node['name']}")
        names.append(node["name"])
        seen.add(node["name"])
    canonical = sorted(names)
    index = {name: i for i, name in enumerate(canonical)}
    remap = [index[name] for name in names]
    links = set()
    for i, edge in enumerate(edges):
        try:
            if len(edge) < 2:
                raise ValueError(f"Edge {i} needs two endpoints")
            a, b = edge[0], edge[1]
        except (TypeError, IndexError, KeyError) as error:
            raise ValueError(f"Malformed edge {i}") from error
        if type(a) is not int or type(b) is not int or not (0 <= a < len(names) and 0 <= b < len(names)):
            raise ValueError(f"Invalid endpoint indices on edge {i}")
        if a != b:
            links.add(tuple(sorted((remap[a], remap[b]))))
    return canonical, sorted(links)


@lru_cache(maxsize=1)
def tool_versions():
    result = {
        "python_igraph": importlib.metadata.version("igraph"),
        "leidenalg": importlib.metadata.version("leidenalg"),
        "igraph_c": igraph.__igraph_version__,
    }
    for engine in ("neato", "sfdp"):
        executable = shutil.which(engine)
        if executable is None:
            raise RuntimeError(f"Graphviz executable not found: {engine}")
        run = subprocess.run([executable, "-V"], capture_output=True, text=True, check=True)
        result[engine] = (run.stdout + run.stderr).strip()
    return result


def _graphviz(engine, dot, expected_names):
    run = subprocess.run([engine, "-Tplain"], input=dot, capture_output=True, text=True, timeout=300)
    if run.returncode:
        raise RuntimeError(f"{engine} failed: {run.stderr[-2000:]}")
    positions = {}
    for line in run.stdout.splitlines():
        if line.startswith("node "):
            fields = line.split()
            name, x, y = fields[1], float(fields[2]), float(fields[3])
            if name in positions or not (math.isfinite(x) and math.isfinite(y)):
                raise RuntimeError(f"Invalid {engine} coordinate for {name}")
            positions[name] = (x, y)
    if set(positions) != set(expected_names):
        raise RuntimeError(f"{engine} omitted or added layout nodes")
    return positions


def _partition(names, links, resolution=RESOLUTION):
    graph = igraph.Graph(n=len(names), edges=links, directed=False)
    if not links:
        return [[i] for i in range(len(names))], 0.0, 0.0
    partition = leidenalg.find_partition(
        graph, leidenalg.RBConfigurationVertexPartition,
        resolution_parameter=resolution, seed=SEED, n_iterations=-1,
    )
    groups = sorted((sorted(members) for members in partition), key=lambda members: names[members[0]])
    return groups, float(graph.modularity(partition.membership)), float(partition.quality())


def partition_statistics(nodes, edges, resolution=RESOLUTION):
    """Cheap relative to geometry; useful for explicitly reported sensitivity."""
    names, links = _canonical_graph(nodes, edges)
    groups, modularity, quality = _partition(names, links, resolution)
    sizes = sorted(map(len, groups), reverse=True)
    return {"resolution": resolution, "community_count": len(groups), "largest_sizes": sizes[:12],
            "singleton_count": sizes.count(1), "modularity": modularity, "rb_quality": quality,
            "undirected_edges": len(links)}


def layout(nodes, edges):
    """Return finite coordinates, canonical communities and versioned statistics.

    Every coordinate is freshly computed. At most four local Graphviz processes
    run together. The supplied node and edge data are never modified.
    Community edge counts refer to unique undirected non-self dependency links.
    """
    names, links = _canonical_graph(nodes, edges)
    versions = dict(tool_versions())
    groups, modularity, quality = _partition(names, links)
    membership = [0] * len(names)
    for community, members in enumerate(groups):
        for member in members:
            membership[member] = community
    internal = [[] for _ in groups]
    boundary = [0] * len(groups)
    cross = Counter()
    for a, b in links:
        ca, cb = membership[a], membership[b]
        if ca == cb:
            internal[ca].append((a, b))
        else:
            boundary[ca] += 1
            boundary[cb] += 1
            cross[tuple(sorted((ca, cb)))] += 1
    radii = [math.sqrt(len(members)) for members in groups]
    if len(groups) > 1:
        dot = ["graph G {", f'graph [start={SEED}, overlap=prism, sep="+12", pack=true];',
               'node [shape=circle, fixedsize=true, label="", margin=0];']
        for community, radius in enumerate(radii):
            diameter = 2 * PACKING_FACTOR * radius
            dot.append(f"c{community} [width={diameter:.12g}, height={diameter:.12g}];")
        for (a, b), weight in sorted(cross.items()):
            length = PACKING_FACTOR * (radii[a] + radii[b]) + 1
            dot.append(f"c{a} -- c{b} [weight={weight}, len={length:.12g}];")
        dot.append("}")
        coarse = _graphviz("neato", "\n".join(dot), [f"c{i}" for i in range(len(groups))])
        centers = [coarse[f"c{i}"] for i in range(len(groups))]
    else:
        centers = [(0.0, 0.0)] * len(groups)
    for a in range(len(groups)):
        for b in range(a):
            distance = math.dist(centers[a], centers[b])
            if distance + 1e-7 < radii[a] + radii[b]:
                raise RuntimeError(f"Community circles overlap after neato: {a}, {b}")

    def local_layout(community):
        members = groups[community]
        if len(members) == 1:
            return [(members[0], 0.0, 0.0)]
        local_index = {member: i for i, member in enumerate(members)}
        dot = ["graph G {", f"graph [start={SEED}, overlap=prism, pack=true];",
               'node [shape=point, width=0.02, height=0.02, label=""];']
        dot.extend(f"n{i};" for i in range(len(members)))
        dot.extend(f"n{local_index[a]} -- n{local_index[b]};" for a, b in internal[community])
        dot.append("}")
        raw = _graphviz("sfdp", "\n".join(dot), [f"n{i}" for i in range(len(members))])
        ordered = [raw[f"n{i}"] for i in range(len(members))]
        mean_x = math.fsum(x for x, _ in ordered) / len(ordered)
        mean_y = math.fsum(y for _, y in ordered) / len(ordered)
        shifted = [(x - mean_x, y - mean_y) for x, y in ordered]
        extent = max(math.hypot(x, y) for x, y in shifted)
        if extent == 0:
            raise RuntimeError("sfdp collapsed a non-singleton community")
        scale = LOCAL_DISK_FACTOR * radii[community] / extent
        return [(member, x * scale, y * scale) for member, (x, y) in zip(members, shifted)]

    positions = {}
    if groups:
        with ThreadPoolExecutor(max_workers=min(MAX_WORKERS, len(groups))) as pool:
            for community, local in enumerate(pool.map(local_layout, range(len(groups)))):
                cx, cy = centers[community]
                for member, x, y in local:
                    px, py = cx + x, cy + y
                    if not (math.isfinite(px) and math.isfinite(py)):
                        raise RuntimeError("Non-finite final node coordinate")
                    positions[names[member]] = {"x": px, "y": py, "community": community}
    positions = {name: positions[name] for name in names}
    communities = [
        {"id": i, "x": centers[i][0], "y": centers[i][1], "radius": radii[i],
         "size": len(members), "internal_edges": len(internal[i]), "boundary_edges": boundary[i]}
        for i, members in enumerate(groups)
    ]
    statistics = {
        "algorithm_version": ALGORITHM_VERSION, "algorithm": "Leiden RBConfigurationVertexPartition",
        "resolution": RESOLUTION, "seed": SEED, "n_iterations": -1, "versions": versions,
        "node_count": len(names), "undirected_edge_count": len(links), "community_count": len(groups),
        "largest_community_size": max(map(len, groups), default=0),
        "singleton_community_count": sum(len(members) == 1 for members in groups),
        "cross_community_edges": sum(cross.values()), "coarse_layout_edge_count": len(cross),
        "modularity": modularity, "rb_quality": quality, "max_layout_workers": MAX_WORKERS,
        "community_radius": "sqrt(member count)", "packing_factor": PACKING_FACTOR,
        "local_disk_factor": LOCAL_DISK_FACTOR,
        "geometry": "packed structural-community presentation; not mathematical distance",
        "edge_counts": "unique undirected non-self dependency links; aggregate links are layout-only",
        "community_id_order": "zero-based, sorted by smallest member full declaration name",
    }
    return {"positions": positions, "communities": communities, "statistics": statistics}
