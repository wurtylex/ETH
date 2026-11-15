#!/usr/bin/env python3
"""Serve only a checked graph bundle on loopback; no API or directory listings."""
import argparse
import gzip
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import json
import mimetypes
from pathlib import Path, PurePosixPath
from urllib.parse import unquote, urlsplit

from build import ALIASES, ASSETS, HERE, digest, require


def safe_file(site, relative):
    part = PurePosixPath(relative)
    require(not part.is_absolute() and '..' not in part.parts and bool(part.parts), 'Invalid asset path')
    path = site / relative
    require(path.resolve().is_relative_to(site.resolve()), 'Asset escaped the site directory')
    for component in (path, *path.parents):
        require(not component.is_symlink(), 'Asset symlinks are unsupported')
        if component == site:
            break
    require(path.is_file(), 'Missing published asset: ' + relative)
    return path


def checked_bytes(site, name, record):
    data = safe_file(site, name).read_bytes()
    require(len(data) == record['bytes'] and digest(data) == record['sha256'], 'Asset hash mismatch: ' + name)
    return data


def load_routes(bundle):
    bundle = Path(bundle).resolve()
    manifest_bytes = (bundle / 'export-manifest.json').read_bytes()
    manifest = json.loads(manifest_bytes)
    require(manifest['status'] == 'passed' and set(manifest['files']) == ASSETS, 'Unexpected publication allowlist')
    require(set(manifest.get('gzip', {})) <= ASSETS, 'Unexpected compressed asset')
    routes, site = {}, bundle / 'site'
    for name, record in manifest['files'].items():
        data = checked_bytes(site, name, record)
        mime = mimetypes.guess_type(name)[0] or 'application/octet-stream'
        if mime.startswith('text/') or mime == 'application/json':
            mime += '; charset=utf-8'
        item = {'data': data, 'sha256': record['sha256'], 'mime': mime}
        if name in manifest.get('gzip', {}):
            packed_record = manifest['gzip'][name]
            require(packed_record['path'] == name + '.gz', 'Unexpected compressed asset path')
            packed = checked_bytes(site, packed_record['path'], packed_record)
            require(gzip.decompress(packed) == data, 'Compressed payload differs')
            item['gzip'] = {'data': packed, 'sha256': packed_record['sha256']}
        routes['/' + name] = item
    for alias, name in ALIASES.items():
        routes[alias] = routes['/' + name]
    # Keep immutable bytes in memory: rebuilding dist cannot change responses
    # underneath an already running server or invalidate its lengths/hashes.
    return routes, digest(manifest_bytes)


def accepts_gzip(header):
    qualities = {}
    for token in header.split(','):
        name, *parameters = token.strip().split(';')
        quality = 1.0
        for parameter in parameters:
            if parameter.strip().startswith('q='):
                try:
                    quality = float(parameter.strip()[2:])
                except ValueError:
                    quality = 0
        qualities[name.lower()] = quality
    return qualities.get('gzip', qualities.get('*', 0)) > 0


class Handler(BaseHTTPRequestHandler):
    server_version = 'ETHGraphs/2.0'
    sys_version = ''

    def do_GET(self):
        self.respond(False)

    def do_HEAD(self):
        self.respond(True)

    def respond(self, head):
        item = self.server.routes.get(unquote(urlsplit(self.path).path))
        if item is None:
            self.send_error(404, 'Not a published graph asset')
            return
        chosen = item['gzip'] if 'gzip' in item and accepts_gzip(self.headers.get('Accept-Encoding', '')) else item
        self.send_response(200)
        self.send_header('Content-Type', item['mime'])
        self.send_header('Content-Length', str(len(chosen['data'])))
        self.send_header('ETag', '"' + chosen['sha256'] + '"')
        self.send_header('X-ETH-Export', self.server.export_manifest_sha256)
        self.send_header('Cache-Control', 'no-cache')
        self.send_header('Vary', 'Accept-Encoding')
        self.send_header('Access-Control-Allow-Origin', '*')
        self.send_header('X-Content-Type-Options', 'nosniff')
        self.send_header('X-Robots-Tag', 'noindex')
        self.send_header('Referrer-Policy', 'no-referrer')
        if chosen is not item:
            self.send_header('Content-Encoding', 'gzip')
        self.end_headers()
        if not head:
            try:
                self.wfile.write(chosen['data'])
            except (BrokenPipeError, ConnectionResetError):
                pass


def make_server(bundle, port):
    routes, checksum = load_routes(bundle)
    server = ThreadingHTTPServer(('127.0.0.1', port), Handler)
    server.daemon_threads = True
    server.routes = routes
    server.export_manifest_sha256 = checksum
    return server


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bundle', type=Path, default=HERE / 'dist')
    parser.add_argument('--port', type=int, default=8768)
    args = parser.parse_args()
    server = make_server(args.bundle, args.port)
    print(f'Serving approved graph assets at http://127.0.0.1:{server.server_port}', flush=True)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        server.server_close()
