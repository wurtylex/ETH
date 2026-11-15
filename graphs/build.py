#!/usr/bin/env python3
"""Recreate the frozen graph website with Python only; never run Lean or layout."""
import argparse
import gzip
import hashlib
import io
import json
import os
from pathlib import Path
import re
import zipfile

HERE = Path(__file__).resolve().parent
ASSETS = frozenset({
    'index.html', 'all/index.html', 'without-openai/index.html',
    'all/graph.json', 'without-openai/graph.json',
    'all/preview.png', 'without-openai/preview.png',
    'method.txt', 'graph-summary.json', 'slide-assets.zip', 'robots.txt',
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
    for key in ('all', 'without-openai'):
        raw = gzip.decompress(inputs['snapshots/' + key + '.graph.json.gz'])
        data = json.loads(raw)
        require(data['meta']['lean_version'] == '4.35.0', 'Unexpected graph compiler')
        template = inputs['templates/' + key + '.html'].decode()
        require(template.count('@@GRAPH_DATA@@') == 1, 'Missing graph placeholder')
        embedded = raw.decode().replace('<', '\\u003c').replace('\u2028', '\\u2028').replace('\u2029', '\\u2029')
        assets[key + '/index.html'] = template.replace('@@GRAPH_DATA@@', embedded).encode()
        assets[key + '/graph.json'] = raw
        assets[key + '/preview.png'] = inputs['previews/' + key + '.png']
    # Container compression can differ across Python/zlib versions. Its four
    # member payloads, names, timestamps and permissions are fixed.
    archive = io.BytesIO()
    with zipfile.ZipFile(archive, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as out:
        for name in ('all/preview.png', 'without-openai/preview.png', 'method.txt', 'graph-summary.json'):
            item = zipfile.ZipInfo(name, (2026, 1, 1, 0, 0, 0))
            item.compress_type = zipfile.ZIP_DEFLATED
            item.external_attr = 0o100644 << 16
            out.writestr(item, assets[name])
    assets['slide-assets.zip'] = archive.getvalue()
    require(set(assets) == ASSETS, 'Unexpected public asset set')
    for name, data in assets.items():
        if name != 'slide-assets.zip':
            expected = snapshot['original_public_assets'][name]
            require(len(data) == expected['bytes'] and digest(data) == expected['sha256'],
                    'Output differs from the verified public snapshot: ' + name)
    routes = set(ALIASES) | {'/' + name for name in ASSETS}
    for name, data in assets.items():
        if name.endswith('.html'):
            for target in re.findall(r'<(?:a|img)\b[^>]*\b(?:href|src)="([^"]+)"', data.decode()):
                require(target in routes, 'Unpublished link: ' + target)
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
