#!/usr/bin/env python3
"""Rebuild original Lean 4.33.1 proof sources and verify frozen theorem endpoints."""
import argparse
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def sha256(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()

def verify_checksums():
    for line in (ROOT / 'SHA256SUMS').read_text().splitlines():
        expected, rel = line.split('  ', 1)
        path = ROOT / rel
        if not path.is_file():
            raise RuntimeError('Missing input: ' + rel + '; run scripts/fetch_dependencies.py first')
        if sha256(path) != expected:
            raise RuntimeError('Input hash mismatch: ' + rel)

def resolve_lean(value):
    found = value or shutil.which('lean')
    if not found:
        raise RuntimeError('Install Lean 4.33.1 or supply --lean /absolute/path/to/bin/lean')
    # Keep an elan shim path intact: resolving it would invoke elan under the wrong name.
    executable = str(Path(found).absolute())
    env = {k: v for k, v in os.environ.items()
           if not k.startswith(('LEAN', 'LAKE')) and k not in ('LD_LIBRARY_PATH', 'LD_PRELOAD', 'DYLD_LIBRARY_PATH')}
    version = subprocess.check_output([executable, '--version'], cwd=ROOT, env=env, text=True).strip()
    if not re.search(r'\bversion 4\.33\.1(?:,|\s|\))', version):
        raise RuntimeError('Expected Lean 4.33.1; got ' + version)
    prefix = Path(subprocess.check_output([executable, '--print-prefix'], cwd=ROOT, env=env, text=True).strip())
    if not (prefix / 'lib/lean').is_dir():
        raise RuntimeError('Missing Lean standard library: ' + str(prefix))
    return executable, prefix, version, env

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--lean', help='Lean 4.33.1 executable; default: lean on PATH')
    p.add_argument('--jobs', type=int, default=2)
    p.add_argument('--lean-threads', type=int, default=1)
    p.add_argument('--timeout', type=int, default=3600, help='Seconds per compiler invocation')
    p.add_argument('--build-dir', default='build-fresh')
    p.add_argument('--verify-checksums', action='store_true', help='Compatibility flag; input checksums are always verified')
    p.add_argument('--verify-only', action='store_true', help='Check existing proof objects and rerun 103 probes; does not recompile proofs')
    args = p.parse_args()
    if min(args.jobs, args.lean_threads, args.timeout) < 1:
        p.error('jobs, lean-threads and timeout must be positive')
    verify_checksums()
    lean, prefix, version, env = resolve_lean(args.lean)
    data = json.loads((ROOT / 'metadata/dependencies.json').read_text())
    modules = set(data['local_modules'])
    actual = {'.'.join(p.relative_to(ROOT / 'Lean').with_suffix('').parts) for p in (ROOT / 'Lean').rglob('*.lean')}
    if modules != actual or len(modules) != 1199:
        raise RuntimeError('Proof source inventory does not match the 1199-module manifest')
    obligations = json.loads((ROOT / 'metadata/original-contract.json').read_text())['spec']['obligations']
    if len(obligations) != 103:
        raise RuntimeError('Expected 103 frozen obligations')
    out = Path(args.build_dir)
    if not out.is_absolute():
        out = ROOT / out
    out = out.resolve()
    if args.verify_only:
        for m in modules:
            if not (out / 'lib/lean' / Path(*m.split('.')).with_suffix('.olean')).is_file():
                raise RuntimeError('Missing existing proof object: ' + m)
    else:
        if out.exists():
            raise RuntimeError('Fresh build directory must not exist: ' + str(out))
        out.mkdir(parents=True)
    obj, logs = out / 'lib/lean', out / 'logs'
    obj.mkdir(parents=True, exist_ok=True)
    logs.mkdir(exist_ok=True)
    env.update(LEAN_PATH=os.pathsep.join(map(str, [obj, ROOT / 'dependencies/lib/lean', prefix / 'lib/lean'])),
               LEAN_SYSROOT=str(prefix), LEAN_NUM_THREADS=str(args.lean_threads))
    deps = {m: set(data['modules'][m]) & modules for m in modules}
    started = time.time()
    results, checks, done, pending, running = [], [], set(), set() if args.verify_only else set(modules), {}
    def run(source, log, target=None):
        command = [lean, '-j' + str(args.lean_threads)]
        if target:
            target.parent.mkdir(parents=True, exist_ok=True)
            command += ['-o', str(target)]
        command.append(str(source))
        t = time.time()
        r = subprocess.run(command, cwd=ROOT / 'Lean', env=env, capture_output=True, text=True, timeout=args.timeout)
        (logs / log).write_text(r.stdout + r.stderr)
        return r, round(time.time() - t, 3)
    def compile_one(m):
        rel = Path(*m.split('.'))
        r, seconds = run(ROOT / 'Lean' / rel.with_suffix('.lean'), m + '.log', obj / rel.with_suffix('.olean'))
        return {'module': m, 'returncode': r.returncode, 'seconds': seconds}
    report = {'passed': False, 'lean_version': version, 'jobs': args.jobs, 'lean_threads': args.lean_threads,
              'dependency_mode': 'Fixed precompiled external libraries; proof sources freshly compiled unless verify-only',
              'input_manifest_sha256': sha256(ROOT / 'SHA256SUMS'), 'allowed_axioms': sorted(ALLOWED)}
    try:
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
            while pending or running:
                ready = sorted(m for m in pending if deps[m] <= done)
                for m in ready[:args.jobs - len(running)]:
                    pending.remove(m)
                    running[pool.submit(compile_one, m)] = m
                if not running:
                    raise RuntimeError('Cyclic local import graph')
                finished, _ = concurrent.futures.wait(running, return_when=concurrent.futures.FIRST_COMPLETED)
                for f in finished:
                    m = running.pop(f)
                    result = f.result()
                    results.append(result)
                    if result['returncode']:
                        raise RuntimeError('Compilation failed; see ' + str(logs / (m + '.log')))
                    done.add(m)
                if len(done) % 25 < len(finished):
                    print('Compiled %d/1199 (%.0fs)' % (len(done), time.time() - started), flush=True)
        def check_one(pair):
            i, item = pair
            r, seconds = run(ROOT / 'verification/probes' / ('%03d.lean' % i), 'exact-%03d.log' % i)
            match = re.search(r'depends on axioms:\s*\[([^]]*)\]', r.stdout)
            used = {x.strip() for x in match.group(1).split(',') if x.strip()} if match else set()
            ok = r.returncode == 0 and (bool(match) or 'does not depend on any axioms' in r.stdout) and used <= ALLOWED
            return {'id': item['id'], 'declaration': item['declaration'], 'passed': ok,
                    'returncode': r.returncode, 'axioms': sorted(used), 'seconds': seconds}
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
            checks = list(pool.map(check_one, enumerate(obligations)))
        if not all(x['passed'] for x in checks):
            raise RuntimeError('Exact type or axiom verification failed; see exact-*.log')
        # A long run must not accept inputs edited after its initial checksum check.
        verify_checksums()
        report['passed'] = True
    except Exception as e:
        report['error'] = str(e)
        raise
    finally:
        report.update(fresh_modules=len(done), verified_existing_modules=len(modules) if args.verify_only else 0,
                      exact_type_checks=len(checks), elapsed_seconds=round(time.time() - started, 3),
                      compiles=results, obligations=checks)
        name = 'ReverificationReport.json' if args.verify_only else 'VerificationReport.json'
        (out / name).write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k not in ('compiles', 'obligations')}, indent=2))

if __name__ == '__main__':
    main()
