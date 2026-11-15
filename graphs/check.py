#!/usr/bin/env python3
"""Check snapshot fidelity and an isolated loopback server; no Lean or tunnel."""
import argparse
import gzip
import http.client
import io
import json
import re
import threading
import zipfile

from build import ASSETS, HERE, build, digest, require
from serve import make_server


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--skip-build', action='store_true', help='Check the existing graphs/dist bundle')
    args = parser.parse_args()
    bundle = HERE / 'dist'
    manifest = json.loads((bundle / 'export-manifest.json').read_text()) if args.skip_build else build(bundle)
    snapshot = json.loads((HERE / 'snapshots/manifest.json').read_text())
    graphs = {}
    for key in ('all', 'without-openai'):
        raw = (bundle / 'site' / key / 'graph.json').read_bytes()
        graphs[key] = json.loads(raw)
        page = (bundle / 'site' / key / 'index.html').read_text()
        match = re.search(r'<script id="graph-data" type="application/json">(.*?)</script>', page, re.S)
        require(match is not None and json.loads(match[1]) == graphs[key], 'Embedded graph differs')
        require(digest(page.encode()) == snapshot['original_public_assets'][key + '/index.html']['sha256'],
                'Renderer/scripts/styles differ from the checked public snapshot')
        for control in ('line-density', 'opacity', 'show-cluster-names', 'export', 'route-focus', 'community-focus'):
            require(f'id="{control}"' in page, 'Missing preserved control: ' + control)
    full, reduced = graphs['all'], graphs['without-openai']
    kept = [i for i, node in enumerate(full['nodes']) if node['membership'] != 1]
    remap = {old: new for new, old in enumerate(kept)}
    require([n['name'] for n in reduced['nodes']] == [full['nodes'][i]['name'] for i in kept], 'Subset membership differs')
    require(reduced['edges'] == [[remap[a], remap[b]] for a, b in full['edges'] if a in remap and b in remap],
            'Subset direct references differ')
    require(reduced['edgeFlags'] == [flag for (a, b), flag in zip(full['edges'], full['edgeFlags']) if a in remap and b in remap],
            'Subset reference flags differ')
    for before, after in zip((full['nodes'][i] for i in kept), reduced['nodes']):
        for field in ('name', 'module', 'kind', 'has_value', 'membership', 'proof_membership', 'raw_index'):
            require(before[field] == after[field], 'Source node field differs: ' + field)
        require(after['display_membership'] == (after['membership'] & 6), 'Reduced display membership differs')
    for graph, expected in ((full, (61514, 453353, 72)), (reduced, (15111, 95461, 37))):
        require((len(graph['nodes']), len(graph['edges']), len(graph['meta']['communities'])) == expected,
                'Unexpected snapshot counts')
        require(graph['meta']['lean_version'] == '4.35.0' and not graph['meta']['exact_manuscript_algorithm_verified'],
                'Proof scope changed')
    with zipfile.ZipFile(io.BytesIO((bundle / 'site/slide-assets.zip').read_bytes())) as archive:
        expected = {'all/preview.png', 'without-openai/preview.png', 'method.txt', 'graph-summary.json'}
        require(set(archive.namelist()) == expected, 'Unexpected slide archive member')
        for name in expected:
            require(archive.read(name) == (bundle / 'site' / name).read_bytes(), 'Slide archive content differs')
    server = make_server(bundle, 0)
    # This isolated test server uses an ephemeral port, never the live origin.
    server.RequestHandlerClass.log_message = lambda *_: None
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    try:
        def request(path, method='GET', headers=None):
            connection = http.client.HTTPConnection('127.0.0.1', server.server_port, timeout=10)
            connection.request(method, path, headers=headers or {})
            response = connection.getresponse()
            result = response.status, dict(response.getheaders()), response.read()
            connection.close()
            return result
        for key in ('all', 'without-openai'):
            status, headers, body = request('/' + key + '/graph.json', headers={'Accept-Encoding': 'gzip'})
            require(status == 200 and headers['Content-Encoding'] == 'gzip', 'Compressed graph unavailable')
            require(digest(gzip.decompress(body)) == manifest['files'][key + '/graph.json']['sha256'], 'HTTP graph payload differs')
        for route, asset in (('/', 'index.html'), ('/all/', 'all/index.html'), ('/without-openai/', 'without-openai/index.html')):
            status, headers, body = request(route, 'HEAD')
            require(status == 200 and not body and int(headers['Content-Length']) == manifest['files'][asset]['bytes'],
                    'Navigation/HEAD route failed')
        status, headers, body = request('/graph-summary.json', headers={'Accept-Encoding': 'gzip;q=0, *;q=1'})
        require(status == 200 and 'Content-Encoding' not in headers and digest(body) == manifest['files']['graph-summary.json']['sha256'],
                'Explicit gzip refusal ignored')
        for path in ('/export-manifest.json', '/runtime.json', '/.git/config', '/api/', '/source.py', '/%2e%2e/README.md', '/all/graph.json.gz'):
            require(request(path)[0] == 404, 'Unpublished path was served: ' + path)
        require(request('/graph-summary.json', 'POST')[0] == 501, 'Unexpected write endpoint')
        require(len(server.routes) == len(ASSETS) + 3, 'Unexpected public route count')
    finally:
        server.shutdown()
        server.server_close()
        thread.join(timeout=5)
    print(json.dumps({'status': 'passed', 'assets': len(ASSETS), 'public_routes': len(ASSETS) + 3,
                      'html_json_snapshot_bytes_preserved': True, 'subset_nodes_edges_flags_preserved': True,
                      'isolated_http_allowlist_and_gzip_checked': True, 'lean_executed': False,
                      'live_publication_touched': False}, indent=2))


if __name__ == '__main__':
    main()
