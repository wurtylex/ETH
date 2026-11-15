#!/usr/bin/env python3
"""Manage this repository's temporary local graph server and Cloudflare tunnel."""
import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time
from urllib.request import urlopen

from build import HERE, digest, require
from serve import load_routes

ROOT = HERE.parent
STATE = ROOT / '.scratch/public-graphs'
RUNTIME = STATE / 'runtime.json'
PORT = 8768
# Do not resolve this legacy marker: results/ may now be an archival symlink,
# but the still-running original process retains its original argv spelling.
SERVER_MARKERS = (str(HERE / 'serve.py'), str(ROOT / 'results/Audit/public-graphs/serve.py'))
TUNNEL_MARKERS = (str(STATE / 'empty-config.yml'),)


def owned_alive(pid, markers):
    if type(pid) is not int or pid <= 0:
        return False
    try:
        argv = Path(f'/proc/{pid}/cmdline').read_bytes().split(b'\0')
        return any(marker.encode() in argv for marker in markers)
    except (FileNotFoundError, ProcessLookupError, PermissionError):
        return False


def save(record):
    temporary = RUNTIME.with_suffix('.tmp')
    temporary.write_text(json.dumps(record, indent=2) + '\n')
    os.replace(temporary, RUNTIME)


def status(record):
    result = dict(record)
    result['server_running'] = owned_alive(record.get('server_pid'), SERVER_MARKERS)
    result['tunnel_running'] = owned_alive(record.get('tunnel_pid'), TUNNEL_MARKERS)
    log = STATE / 'tunnel.log'
    if result['tunnel_running'] and log.exists():
        matches = re.findall(r'https://[a-z0-9-]+\.trycloudflare\.com', log.read_text())
        if matches:
            result['public_url'] = matches[-1]
    result['public_running'] = result['server_running'] and result['tunnel_running']
    return result


def stop_owned(record, key):
    markers = SERVER_MARKERS if key == 'server' else TUNNEL_MARKERS
    pid = record.get(key + '_pid')
    if owned_alive(pid, markers):
        try:
            os.kill(pid, signal.SIGTERM)
        except ProcessLookupError:
            return
        for _ in range(100):
            if not owned_alive(pid, markers):
                return
            time.sleep(.1)
        raise RuntimeError(f'{key} is still shutting down; run status before retrying')


def expected_origin(bundle):
    raw = (bundle / 'export-manifest.json').read_bytes()
    manifest = json.loads(raw)
    return digest(raw), manifest['files']['graph-summary.json']['sha256']


def wait_origin(bundle, process=None):
    manifest_sha, summary_sha = expected_origin(bundle)
    for _ in range(50):
        if process is not None and process.poll() is not None:
            raise RuntimeError('Graph server stopped; inspect the private server.log')
        try:
            with urlopen(f'http://127.0.0.1:{PORT}/graph-summary.json', timeout=1) as response:
                require(response.status == 200 and response.headers.get('X-ETH-Export') == manifest_sha,
                        'Port is not serving this approved export')
                require(digest(response.read()) == summary_sha, 'Unexpected origin contents')
            if process is not None and process.poll() is not None:
                raise RuntimeError('Graph server stopped during readiness check')
            return
        except OSError:
            time.sleep(.2)
    raise RuntimeError('Graph server did not become ready')


def start_server(record, bundle):
    # Validate the replacement before touching an existing running server.
    load_routes(bundle)
    stop_owned(record, 'server')
    with (STATE / 'server.log').open('ab') as log:
        child = subprocess.Popen([sys.executable, str(HERE / 'serve.py'), '--bundle', str(bundle), '--port', str(PORT)],
            cwd=ROOT, stdin=subprocess.DEVNULL, stdout=log, stderr=log, start_new_session=True)
    record.update(server_pid=child.pid, bundle=str(bundle))
    save(record)
    wait_origin(bundle, child)


def start_tunnel(record):
    binary = shutil.which('cloudflared')
    require(bool(binary), 'Install cloudflared to share publicly; local serve needs only Python')
    config = STATE / 'empty-config.yml'
    config.write_text('{}\n')
    environment = {k: v for k, v in os.environ.items()
                   if not k.startswith(('TUNNEL_', 'CLOUDFLARED_', 'CLOUDFLARE_'))}
    command = [binary, 'tunnel', '--config', str(config), '--no-autoupdate',
               '--protocol', 'http2', '--metrics', '127.0.0.1:0', '--url', f'http://127.0.0.1:{PORT}']
    record.pop('public_url', None)
    with (STATE / 'tunnel.log').open('wb') as log:
        child = subprocess.Popen(command, cwd=ROOT, env=environment,
            stdin=subprocess.DEVNULL, stdout=log, stderr=log, start_new_session=True)
    record.update(tunnel_pid=child.pid, started_at_utc=datetime.now(timezone.utc).isoformat())
    record.pop('stopped_at_utc', None)
    save(record)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=('start', 'share', 'status', 'stop', 'refresh'))
    parser.add_argument('--bundle', type=Path, default=HERE / 'dist')
    args = parser.parse_args()
    require(Path('/proc/self/cmdline').exists(), 'The detached host manager needs Linux /proc; use serve.py for local viewing elsewhere')
    record = json.loads(RUNTIME.read_text()) if RUNTIME.exists() else {}
    current = status(record)
    if args.action == 'status':
        print(json.dumps(current, indent=2))
        return
    STATE.mkdir(parents=True, exist_ok=True)
    if args.action == 'stop':
        stop_owned(record, 'tunnel')
        stop_owned(record, 'server')
        record['stopped_at_utc'] = datetime.now(timezone.utc).isoformat()
        save(record)
        print(json.dumps(status(record), indent=2))
        return
    if args.action == 'refresh' or not current['server_running']:
        start_server(record, args.bundle.resolve())
    else:
        # An existing legacy server uses STATE as its bundle. Never rebuild or
        # rewrite its serving tree merely to inspect/reuse its current tunnel.
        wait_origin(Path(record.get('bundle', STATE)))
    if not current['tunnel_running']:
        start_tunnel(record)
    for _ in range(60):
        current = status(record)
        require(current['tunnel_running'], 'Tunnel stopped; inspect the private tunnel.log')
        if current.get('public_url'):
            record['public_url'] = current['public_url']
            save(record)
            print(json.dumps(status(record), indent=2))
            return
        time.sleep(.5)
    raise RuntimeError('Tunnel is running but has not supplied a public URL; run status')


if __name__ == '__main__':
    main()
