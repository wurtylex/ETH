#!/usr/bin/env python3
"""Upload this project and verify it over SSH. Never executes Lean/Lake/elan locally."""
import argparse
import hashlib
import io
import json
import os
from pathlib import Path, PurePosixPath
import shlex
import subprocess
import sys
import tarfile
import tempfile

from remote_worker import inventory, sha


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--host', required=True, help='Authorized remote USER@HOST')
    parser.add_argument('--port', type=int, default=22)
    parser.add_argument('--remote-root', required=True, help='New, nonexistent absolute remote workspace')
    parser.add_argument('--cache-project', help='Optional compatible project already on the remote server')
    parser.add_argument('--known-hosts', type=Path)
    parser.add_argument('--threads', type=int, default=16)
    args = parser.parse_args()
    assert args.host and not args.host.startswith('-') and not any(c.isspace() for c in args.host)
    hostname = args.host.rsplit('@', 1)[-1].lower()
    assert hostname not in ['localhost', '127.0.0.1', '::1', '[::1]'], 'Use a remote server, not local SSH'
    assert 0 < args.port < 65536 and 0 < args.threads <= 128
    root = PurePosixPath(args.remote_root)
    assert root.is_absolute() and '..' not in root.parts and len(root.parts) >= 3
    project = Path(__file__).resolve().parents[1]
    output = project / 'audit/verification'
    assert not output.exists(), 'Preserve/move the prior verification directory before another run'
    before = inventory(project)
    ssh = ['ssh', '-F', '/dev/null', '-p', str(args.port), '-o', 'BatchMode=yes',
           '-o', 'ConnectTimeout=15', '-o', 'ServerAliveInterval=30',
           '-o', 'ServerAliveCountMax=6', '-o', 'StrictHostKeyChecking=yes']
    if args.known_hosts:
        ssh += ['-o', 'UserKnownHostsFile=' + str(args.known_hosts.resolve())]
    ssh.append(args.host)
    def remote(argv, **kwargs):
        return subprocess.run([*ssh, shlex.join(argv)], **kwargs)
    extract = '''import sys,tarfile,json
from pathlib import Path,PurePosixPath
r=Path(sys.argv[1]);r.mkdir(parents=True,exist_ok=False);p=r/'lean';p.mkdir()
with tarfile.open(fileobj=sys.stdin.buffer,mode='r|gz') as t:
 for m in t:
  n=PurePosixPath(m.name)
  assert not n.is_absolute() and '..' not in n.parts and m.isfile()
  f=p.joinpath(*n.parts);f.parent.mkdir(parents=True,exist_ok=True)
  with f.open('xb') as out: out.write(t.extractfile(m).read())
  import os
  os.chmod(f,m.mode);os.utime(f,(m.mtime,m.mtime))
print(json.dumps({'status':'source-uploaded'}))
'''
    with tempfile.TemporaryFile() as archive:
        with tarfile.open(fileobj=archive, mode='w:gz') as t:
            for name in sorted(before):
                t.add(project / name, arcname=name, recursive=False)
        archive.seek(0)
        remote(['python3', '-c', extract, str(root)], stdin=archive, check=True)
    worker = ['python3', str(root / 'lean/scripts/remote_worker.py'), '--threads', str(args.threads)]
    if args.cache_project:
        worker += ['--cache-project', args.cache_project]
    print('Source uploaded; remote verification running.', flush=True)
    execution = remote(worker, check=False)
    retrieve = '''import sys,tarfile
from pathlib import Path
p=Path(sys.argv[1])/'verification'
with tarfile.open(fileobj=sys.stdout.buffer,mode='w|gz') as t:
 for f in sorted(p.rglob('*')):
  if f.is_file():
   assert not f.is_symlink()
   t.add(f,arcname=str(f.relative_to(p)),recursive=False)
'''
    result = remote(['python3', '-c', retrieve, str(root)], capture_output=True, check=True)
    output.mkdir()
    with tarfile.open(fileobj=io.BytesIO(result.stdout), mode='r:gz') as t:
        for member in t:
            name = PurePosixPath(member.name)
            assert not name.is_absolute() and '..' not in name.parts and member.isfile()
            destination = output.joinpath(*name.parts)
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(t.extractfile(member).read())
    manifest = json.loads((output / 'manifest.json').read_text())
    for name, item in manifest['files'].items():
        p = output / name
        assert p.stat().st_size == item['bytes'] and sha(p) == item['sha256'], name
    after = inventory(project)
    assert before == after, 'Local source inputs changed during the remote run'
    verification = json.loads((output / 'verification.json').read_text())
    remote_before = json.loads((output / 'source-before.json').read_text())
    assert before == remote_before, 'Uploaded source differs from the local project'
    if verification['status'] == 'passed':
        assert json.loads((output / 'source-after.json').read_text()) == after
    retrieved = {'status': 'passed' if verification['status'] == 'passed' and execution.returncode == 0 else 'failed',
                 'remote_execution_exit_code': execution.returncode, 'local_lean_execution': False,
                 'all_retrieved_hashes_validated': True, 'local_and_uploaded_inputs_equal': True,
                 'local_inputs_unchanged': True, 'source_file_count': len(before),
                 'remote_verification_sha256': sha(output / 'verification.json'),
                 'manifest_sha256': sha(output / 'manifest.json'),
                 'transfer_sha256': hashlib.sha256(result.stdout).hexdigest()}
    (output / 'retrieval.json').write_text(json.dumps(retrieved, indent=2) + '\n')
    print(json.dumps(retrieved, indent=2))
    return 0 if retrieved['status'] == 'passed' else 1


if __name__ == '__main__':
    sys.exit(main())
