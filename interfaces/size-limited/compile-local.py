#!/usr/bin/env python3
"""Compile one published complete interface; no official submission is performed."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess


def main():
    base = Path(__file__).resolve().parent
    repo = base.parents[1]
    manifest = json.loads((base / 'manifest.json').read_text())
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('interface', choices=sorted(manifest['interfaces']))
    args = parser.parse_args()
    selected = base / args.interface
    files = ['Challenge.lean', 'Solution.lean', 'comparator.json']
    bound = {str(selected / f): manifest['files'][args.interface + '/' + f] for f in files}
    support = base / 'support/PointedHodgeCharacterization.lean'
    if args.interface != 'accepted-087':
        bound[str(support)] = manifest['files']['support/PointedHodgeCharacterization.lean']

    def check_sources():
        for p, digest in bound.items():
            if hashlib.sha256(Path(p).read_bytes()).hexdigest() != digest:
                raise RuntimeError('Published source hash mismatch: ' + p)

    check_sources()
    version = subprocess.check_output(['lake', 'env', 'lean', '--version'], cwd=repo, text=True).strip()
    if 'version 4.35.0-rc2' not in version:
        raise RuntimeError('Expected the pinned Lean 4.35.0-rc2 compiler: ' + version)
    prefix = subprocess.check_output(['lake', 'env', 'lean', '--print-prefix'], cwd=repo, text=True).strip()
    path = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=repo, text=True).strip()
    paths = [str((repo / p).resolve()) if not Path(p).is_absolute() else p for p in path.split(os.pathsep) if p]
    output = repo / '.lake/size-limited' / args.interface
    output.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, LEAN_PATH=os.pathsep.join([str(output)] + paths), LEAN_NUM_THREADS='1')
    lean = str(Path(prefix) / 'bin/lean')

    def compile_file(source, root):
        name = source.stem
        subprocess.run([lean, '-j1', '-R', str(root), '-o', str(output / (name + '.olean')),
                        '-i', str(output / (name + '.ilean')), str(source)],
                       cwd=repo, env=env, check=True)

    if args.interface != 'accepted-087':
        compile_file(support, support.parent)
    compile_file(selected / 'Challenge.lean', selected)
    compile_file(selected / 'Solution.lean', selected)
    check_sources()
    receipt = {'interface': args.interface, 'compiler': version, 'compilation_passed': True,
               'source_sha256': bound,
               'scope': 'Compilation only. No fresh Comparator, export, independent kernel, semantic review, or official submission is implied.'}
    (output / 'compilation.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print('Compilation complete; receipt:', output / 'compilation.json')


if __name__ == '__main__':
    main()
