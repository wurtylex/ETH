#!/usr/bin/env python3
"""Render frozen graph data and a curated reading guide; never run Lean or layout."""
import argparse
import gzip
import hashlib
import io
import json
import os
from pathlib import Path
import re
import zipfile
from urllib.parse import urlsplit

HERE = Path(__file__).resolve().parent
ASSETS = frozenset({
    'index.html', 'all/index.html', 'without-openai/index.html',
    'all/graph.json', 'without-openai/graph.json',
    'all/preview.png', 'without-openai/preview.png',
    'method.txt', 'graph-summary.json', 'slide-assets.zip', 'robots.txt',
    'proof-guide.json', 'proof-guide.txt',
})
ALIASES = {'/': 'index.html', '/all/': 'all/index.html',
           '/without-openai/': 'without-openai/index.html'}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def source_file(name):
    path = HERE / name
    require(path.resolve().is_relative_to(HERE), 'Input escaped graphs/')
    return path


def expected_assets(snapshot):
    # Keep the original publication hashes as provenance. Later presentation
    # revisions override only their explicitly listed assets, never graph data.
    revisions = snapshot.get('presentation_assets', {})
    require(set(revisions) <= {'index.html', 'all/index.html', 'without-openai/index.html', 'method.txt',
                               'proof-guide.json', 'proof-guide.txt', 'graph-summary.json',
                               'all/preview.png', 'without-openai/preview.png'},
            'A presentation revision cannot override frozen graph data')
    return {**snapshot['original_public_assets'], **revisions}


def check_guide(guide, graph, raw):
    require(guide['schema_version'] == 1, 'Unsupported proof guide')
    require(guide['graph_json_sha256'] == digest(raw), 'Guide belongs to a different graph')
    require(re.fullmatch(r'[0-9a-f]{40}', guide['source_commit']) is not None, 'Invalid guide source revision')
    nodes = {node['name']: node for node in graph['nodes']}
    ids = set()
    for stage in guide['stages']:
        require(stage['id'] not in ids and re.fullmatch(r'[a-z0-9-]+', stage['id']), 'Invalid/duplicate guide stage')
        ids.add(stage['id'])
        require(1 <= len(stage['anchors']) <= 4, 'A guide stage needs one to four anchors')
        for anchor in stage['anchors']:
            require(anchor['name'] in nodes, 'Guide declaration absent: ' + anchor['name'])
            mask = nodes[anchor['name']]['membership'] & 6
            require(mask == {'ours': 4, 'anthropic': 2, 'shared': 6}[anchor['route']],
                    'Guide route differs from actual reachability: ' + anchor['name'])
            source = anchor['source']
            path = Path(source['path'])
            require(not path.is_absolute() and '..' not in path.parts and source['path'].startswith('lean/'),
                    'Invalid guide source path')
            require(type(source['line']) is int and source['line'] > 0, 'Invalid guide source line')
            require(re.fullmatch(r'[0-9a-f]{64}', source['sha256']) is not None, 'Missing source digest')
            require(source['url'] == 'https://github.com/wurtylex/ETH/blob/' + guide['source_commit'] +
                    '/' + source['path'] + '#L' + str(source['line']), 'Source link is not pinned to the reviewed revision')


def guide_text(guide):
    lines = [guide['title'], '', guide['intro'], '', guide['scope_note'], '']
    for stage in guide['stages']:
        lines.extend([stage['title'], stage['relation'], stage['summary'], stage['comparison'], ''])
        for anchor in stage['anchors']:
            lines.extend([f"  {anchor['route'].upper()}: {anchor['label']}", '  ' + anchor['name'],
                          '  ' + anchor['description'], '  ' + anchor['source']['url'], ''])
        for source in stage.get('supporting_sources', []):
            lines.extend(['  Additional statement evidence: ' + source['url'], ''])
    return ('\n'.join(lines) + '\n').encode()


def make_assets():
    snapshot_bytes = (HERE / 'snapshots/manifest.json').read_bytes()
    snapshot = json.loads(snapshot_bytes)
    require(snapshot['lean_version'] == '4.35.0', 'Unexpected snapshot compiler')
    inputs = {}
    for name, record in snapshot['inputs'].items():
        data = source_file(name).read_bytes()
        require(len(data) == record['bytes'] and digest(data) == record['sha256'],
                'Changed snapshot input: ' + name)
        inputs[name] = data
    assets = {'index.html': inputs['templates/index.html'],
              'method.txt': inputs['method.txt'], 'robots.txt': inputs['robots.txt'],
              'graph-summary.json': inputs['snapshots/graph-summary.json']}
    guide_raw = inputs['annotations/anthropic-ours.json']
    guide = json.loads(guide_raw)
    assets['proof-guide.json'] = guide_raw
    assets['proof-guide.txt'] = guide_text(guide)
    for key in ('all', 'without-openai'):
        raw = gzip.decompress(inputs['snapshots/' + key + '.graph.json.gz'])
        data = json.loads(raw)
        require(data['meta']['lean_version'] == '4.35.0', 'Unexpected graph compiler')
        template = inputs['templates/' + key + '.html'].decode()
        require(template.count('@@GRAPH_DATA@@') == 1, 'Missing graph placeholder')
        if key == 'without-openai':
            check_guide(guide, data, raw)
            require(template.count('@@PROOF_GUIDE@@') == 1, 'Missing proof guide placeholder')
            safe_guide = guide_raw.decode().replace('<', '\\u003c').replace('\u2028', '\\u2028').replace('\u2029', '\\u2029')
            template = template.replace('@@PROOF_GUIDE@@', safe_guide)
        embedded = raw.decode().replace('<', '\\u003c').replace('\u2028', '\\u2028').replace('\u2029', '\\u2029')
        assets[key + '/index.html'] = template.replace('@@GRAPH_DATA@@', embedded).encode()
        assets[key + '/graph.json'] = raw
        assets[key + '/preview.png'] = inputs['previews/' + key + '.png']
    # Container compression can differ across Python/zlib versions. Its six
    # member payloads, names, timestamps and permissions are fixed.
    archive = io.BytesIO()
    with zipfile.ZipFile(archive, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as out:
        for name in ('all/preview.png', 'without-openai/preview.png', 'method.txt', 'graph-summary.json',
                     'proof-guide.json', 'proof-guide.txt'):
            item = zipfile.ZipInfo(name, (2026, 1, 1, 0, 0, 0))
            item.compress_type = zipfile.ZIP_DEFLATED
            item.external_attr = 0o100644 << 16
            out.writestr(item, assets[name])
    assets['slide-assets.zip'] = archive.getvalue()
    require(set(assets) == ASSETS, 'Unexpected public asset set')
    for name, data in assets.items():
        if name != 'slide-assets.zip':
            expected = expected_assets(snapshot)[name]
            require(len(data) == expected['bytes'] and digest(data) == expected['sha256'],
                    'Output differs from the pinned graph/presentation assets: ' + name)
    routes = set(ALIASES) | {'/' + name for name in ASSETS}
    for name, data in assets.items():
        if name.endswith('.html'):
            for target in re.findall(r'<(?:a|img)\b[^>]*\b(?:href|src)="([^"]+)"', data.decode()):
                link = urlsplit(target)
                require(not link.scheme and not link.netloc and link.path in routes, 'Unpublished link: ' + target)
    return assets, digest(snapshot_bytes)


def atomic_write(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + '.tmp')
    temporary.write_bytes(data)
    os.replace(temporary, path)


def build(output):
    output = Path(output).resolve()
    legacy = HERE.parent / '.scratch/public-graphs'
    require(not output.is_relative_to(legacy.resolve()),
            'The existing live publication tree is reserved; build graphs/dist instead')
    assets, snapshot_sha = make_assets()
    compressed_names = {name for name in ASSETS if name.endswith(('.html', '.json', '.txt'))}
    allowed = {'export-manifest.json'} | {'site/' + name for name in ASSETS}
    allowed |= {'site/' + name + '.gz' for name in compressed_names}
    if output.exists():
        existing = {str(p.relative_to(output)) for p in output.rglob('*') if p.is_file()}
        require(existing <= allowed, 'Output directory contains unrelated files')
        require(not any(p.is_symlink() for p in output.rglob('*')), 'Output directory contains symlinks')
    manifest = {'schema_version': 1, 'status': 'passed', 'public_asset_count': len(assets),
                'kind': 'frozen_lean435_snapshot_render', 'snapshot_manifest_sha256': snapshot_sha,
                'new_lean_verification': False, 'layout_recomputed': False,
                'files': {}, 'gzip': {}}
    for name, data in sorted(assets.items()):
        atomic_write(output / 'site' / name, data)
        manifest['files'][name] = {'bytes': len(data), 'sha256': digest(data)}
        if name in compressed_names:
            packed = gzip.compress(data, compresslevel=9, mtime=0)
            atomic_write(output / 'site' / (name + '.gz'), packed)
            manifest['gzip'][name] = {'path': name + '.gz', 'bytes': len(packed), 'sha256': digest(packed)}
    atomic_write(output / 'export-manifest.json', (json.dumps(manifest, indent=2) + '\n').encode())
    return manifest


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=HERE / 'dist', help='Bundle directory (default: graphs/dist)')
    args = parser.parse_args()
    record = build(args.output)
    print(json.dumps({'status': record['status'], 'assets': record['public_asset_count'],
                      'output': str(args.output.resolve()), 'new_lean_verification': False}))
