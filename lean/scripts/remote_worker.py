#!/usr/bin/env python3
"""Internal verifier. Refuses local execution; launched over SSH by verify_remote.py."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
import traceback


TOOLCHAIN = 'leanprover/lean4:v4.35.0'
OMIT_DIRS = {'.lake', '.git', '__pycache__', 'build', 'lake-packages'}


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


def write(path, data):
    Path(path).write_text(json.dumps(data, indent=2) + '\n')


def inventory(project):
    result = {}
    for base, dirs, files in os.walk(project):
        dirs[:] = sorted(d for d in dirs if d not in OMIT_DIRS and
                         not (Path(base) == project / 'audit' and d == 'verification'))
        for name in sorted(files):
            p = Path(base) / name
            if name.endswith('.pyc'):
                continue
            assert not p.is_symlink(), 'Unexpected source symlink'
            result[str(p.relative_to(project))] = sha(p)
    return result


def seed_cache(source, project):
    """Independent copies: no shared writable cache files or directory symlinks."""
    source = source.resolve()
    assert source != project and not source.is_relative_to(project)
    assert (source / 'lean-toolchain').read_text().strip() == TOOLCHAIN
    assert (source / 'lake-manifest.json').read_bytes() == (project / 'lake-manifest.json').read_bytes()
    def ignore(_directory, names):
        return [name for name in names if name.endswith('.setup.json') or name == '__pycache__']
    copied = []
    for relative in ['.lake/packages', '.lake/build',
                     'vendor/complexitylib/.lake/build', 'vendor/cslib/.lake/build']:
        src, dst = source / relative, project / relative
        if not src.exists():
            continue
        # Exclude regenerable Lean command setup JSON (19 GB in the source cache).
        size = sum(p.stat().st_size for p in src.rglob('*')
                   if p.is_file() and not p.name.endswith('.setup.json'))
        assert shutil.disk_usage(project).free > size + 1024 ** 3, 'Insufficient disk for isolated cache copy'
        shutil.copytree(src, dst, symlinks=True, ignore=ignore)
        copied.append({'directory': relative, 'input_bytes_without_setup_json': size})
    return {'mode': 'independent filesystem copies', 'copied': copied,
            'omitted_artifacts': ['*.setup.json'], 'historical_sources_and_evidence_modified': False}


def main():
    if not os.environ.get('SSH_CONNECTION'):
        raise SystemExit('Remote-only verifier: use scripts/verify_remote.py with an authorized SSH host.')
    parser = argparse.ArgumentParser()
    parser.add_argument('--cache-project', type=Path)
    parser.add_argument('--threads', type=int, default=16)
    args = parser.parse_args()
    project = Path(__file__).resolve().parents[1]
    out = project.parent / 'verification'
    out.mkdir(exist_ok=False)
    (out / 'logs').mkdir()
    plan = json.loads((project / 'audit/plan.json').read_text())
    state = {'schema_version': 1, 'status': 'running', 'local_lean_execution': False,
             'target_toolchain': TOOLCHAIN, 'started_at_utc': datetime.now(timezone.utc).isoformat(),
             'commands': [], 'plan_sha256': sha(project / 'audit/plan.json'),
             'provenance_sha256': sha(project / 'audit/source-provenance.json'),
             'endpoints': plan['endpoints'], 'additional_target': plan['additional_target'],
             'third_route_scope': 'Two-piece implementation variant; exact manuscript algorithm remains separate.'}
    def save():
        state['updated_at_utc'] = datetime.now(timezone.utc).isoformat()
        write(out / 'verification.json', state)
    save()
    try:
        assert (project / 'lean-toolchain').read_text().strip() == TOOLCHAIN
        before = inventory(project)
        write(out / 'source-before.json', before)
        assert sha(project / 'audit/baseline-types.json') == plan['baseline_types_sha256']
        copied = json.loads((project / 'audit/source-inventory.json').read_text())
        lean_sources = {n: h for n, h in copied.items() if n.endswith('.lean')}
        assert all(before.get(n) == h for n, h in lean_sources.items())
        state['copied_lean_sources_unchanged'] = len(lean_sources)
        state['phase'] = 'cache preparation'
        save()
        if args.cache_project:
            state['cache'] = seed_cache(args.cache_project, project)
        else:
            state['cache'] = {'mode': 'cold remote build'}
        toolroot = Path(os.environ.get('ELAN_HOME', str(Path.home() / '.elan'))) / 'toolchains/leanprover--lean4---v4.35.0/bin'
        assert (toolroot / 'lean').is_file() and (toolroot / 'lake').is_file(), 'Install exact Lean 4.35.0 on the remote server first'
        env = os.environ.copy()
        for key in ['LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT']:
            env.pop(key, None)
        env.update(ELAN_TOOLCHAIN=TOOLCHAIN, LEAN_NUM_THREADS=str(args.threads),
                   PATH=str(toolroot) + ':' + env.get('PATH', ''),
                   XDG_CACHE_HOME=str(project.parent / 'cache'),
                   LAKE_CACHE_DIR=str(project.parent / 'cache/lake'))
        def run(argv, name):
            state['phase'] = name
            save()
            started = time.monotonic()
            log = out / 'logs' / (name + '.log')
            actual = [str(toolroot / argv[0]), *argv[1:]] if argv[0] in ['lean', 'lake'] else argv
            with log.open('xb') as f:
                code = subprocess.run(actual, cwd=project, env=env, stdout=f,
                                      stderr=subprocess.STDOUT).returncode
            state['commands'].append({'argv': argv, 'exit_code': code,
                                      'log': str(log.relative_to(out)), 'log_sha256': sha(log),
                                      'elapsed_seconds': round(time.monotonic() - started, 3)})
            save()
            assert code == 0, name + ' failed; inspect its recorded log'
            return log.read_text()
        state['compiler_version'] = run(['lean', '--version'], 'compiler-version').strip()
        assert state['compiler_version'].startswith('Lean (version 4.35.0,')
        state['compiler_sha256'] = sha(toolroot / 'lean')
        run(['lake', 'build'], 'default-build')
        # Git packages must still be exactly the lockfile's commits; caches are ignored.
        lock = json.loads((project / 'lake-manifest.json').read_text())
        pins = {}
        for package in lock['packages']:
            if package['type'] != 'git':
                continue
            directory = project / '.lake/packages' / package['name']
            revision = subprocess.check_output(['git', '-C', str(directory), 'rev-parse', 'HEAD'], text=True).strip()
            assert revision == package['rev'], 'Dependency revision changed: ' + package['name']
            assert not subprocess.check_output(['git', '-C', str(directory), 'status', '--porcelain', '--untracked-files=no'], text=True).strip(), 'Modified dependency source: ' + package['name']
            pins[package['name']] = revision
        state['dependency_revisions'] = pins
        run(['lake', 'env', 'lean', 'audit/CheckEndpoints.lean'], 'endpoint-applications')
        run(['lake', 'env', 'lean', 'audit/CheckC1.lean'], 'wordram-application')
        text = run(['lake', 'env', 'lean', 'audit/CheckMigrationAxioms.lean'], 'axioms')
        text += '\n' + run(['lake', 'env', 'lean', 'audit/CheckMigrationPrivateAxioms.lean'], 'private-axioms')
        axioms = {}
        for name, body in re.findall(r"'([^\n]+)' depends on axioms: \[([^\]]*)\]", text):
            assert name not in axioms
            axioms[name] = sorted(x.strip() for x in body.split(',') if x.strip())
        for name in re.findall(r"'([^\n]+)' does not depend on any axioms", text):
            assert name not in axioms
            axioms[name] = []
        assert set(axioms) == set(plan['expected_axiom_names']), 'Axiom declaration set changed'
        assert all(set(a) <= set(plan['standard_axioms']) for a in axioms.values()), 'Nonstandard axiom detected'
        write(out / 'axioms.json', axioms)
        state.update(axiom_count=len(axioms), standard_axioms_only=True)
        run(['lake', 'env', 'lean', '--run', 'audit/ExtractMigrationTypes.lean',
             '../verification/types-current.json'], 'compiled-types')
        old = json.loads((project / 'audit/baseline-types.json').read_text())
        new = json.loads((out / 'types-current.json').read_text())
        a = {d['name']: d['normalized_type'] for d in old['declarations']}
        b = {d['name']: d['normalized_type'] for d in new['declarations']}
        assert set(a) == set(b) and len(a) == plan['baseline_type_count']
        changed = [n for n in a if a[n] != b[n]]
        comparison = {'status': 'equal' if not changed else 'different', 'declaration_count': len(a),
                      'equal_count': len(a) - len(changed), 'changed_theorems': changed,
                      'baseline_sha256': sha(project / 'audit/baseline-types.json'),
                      'current_sha256': sha(out / 'types-current.json')}
        write(out / 'type-comparison.json', comparison)
        assert not changed, 'Compiled declaration types changed'
        after = inventory(project)
        write(out / 'source-after.json', after)
        assert before == after, 'Project inputs changed during verification'
        state.update(status='passed', phase='complete', exit_code=0,
                     source_inputs_unchanged=True, source_inventory_sha256=sha(out / 'source-after.json'),
                     type_comparison=comparison, dependency_manifest=lock)
    except BaseException as error:
        state.update(status='failed', exit_code=1, error=str(error), traceback=traceback.format_exc())
    state['finished_at_utc'] = datetime.now(timezone.utc).isoformat()
    save()
    files = {str(p.relative_to(out)): {'sha256': sha(p), 'bytes': p.stat().st_size}
             for p in sorted(out.rglob('*')) if p.is_file()}
    write(out / 'manifest.json', {'status': state['status'], 'files': files})
    print(json.dumps({'status': state['status'], 'phase': state['phase']}), flush=True)
    return state['exit_code']


if __name__ == '__main__':
    sys.exit(main())
