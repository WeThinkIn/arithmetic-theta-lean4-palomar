#!/usr/bin/env python3
"""Download hash-pinned GitHub Release assets and materialize dependencies/lib/lean."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import shutil
import stat
import urllib.request
import zipfile

ROOT = Path(__file__).resolve().parents[1]

def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for b in iter(lambda: f.read(1024 * 1024), b''):
            h.update(b)
    return h.hexdigest()

def unpack(archive, root, expected):
    with zipfile.ZipFile(archive) as z:
        for info in z.infolist():
            rel = info.filename
            path = PurePosixPath(rel)
            if (rel not in expected or path.is_absolute() or '..' in path.parts
                    or not rel.startswith('dependencies/lib/lean/')
                    or stat.S_ISLNK(info.external_attr >> 16)):
                raise RuntimeError('Unexpected dependency archive entry: ' + rel)
            target = root / rel
            if target.resolve() != target.absolute():
                raise RuntimeError('Dependency path traverses a symlink: ' + rel)
            if target.exists():
                if digest(target) != expected[rel]:
                    raise RuntimeError('Existing dependency differs; refusing to overwrite: ' + rel)
                continue
            target.parent.mkdir(parents=True, exist_ok=True)
            temp = target.with_name(target.name + '.partial')
            try:
                with z.open(info) as source, temp.open('xb') as dest:
                    shutil.copyfileobj(source, dest)
                if digest(temp) != expected[rel]:
                    raise RuntimeError('Extracted file checksum mismatch: ' + rel)
                temp.replace(target)
            finally:
                if temp.exists():
                    temp.unlink()

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--asset-dir', type=Path, help='Use already downloaded assets; no network')
    p.add_argument('--cache-dir', type=Path, default=ROOT / '.downloads')
    a = p.parse_args()
    expected = {rel: h for h, rel in (line.split('  ', 1) for line in (ROOT / 'SHA256SUMS').read_text().splitlines())
                if rel.startswith('dependencies/lib/lean/')}
    manifest = json.loads((ROOT / 'metadata/dependency-assets.json').read_text())
    folder = a.asset_dir or a.cache_dir
    folder.mkdir(parents=True, exist_ok=True)
    for asset in manifest['assets']:
        file = folder / asset['name']
        if not file.exists():
            if a.asset_dir:
                raise RuntimeError('Missing downloaded asset: ' + str(file))
            temp = file.with_name(file.name + '.partial')
            print('Downloading ' + asset['name'], flush=True)
            try:
                request = urllib.request.Request(asset['url'], headers={'User-Agent': 'arithmetic-theta-local-reproduction'})
                with urllib.request.urlopen(request, timeout=120) as source, temp.open('wb') as dest:
                    shutil.copyfileobj(source, dest)
                if temp.stat().st_size != asset['bytes'] or digest(temp) != asset['sha256']:
                    raise RuntimeError('Downloaded asset checksum mismatch: ' + asset['name'])
                temp.replace(file)
            finally:
                if temp.exists():temp.unlink()
        if file.stat().st_size != asset['bytes'] or digest(file) != asset['sha256']:
            raise RuntimeError('Asset checksum mismatch: ' + asset['name'])
        unpack(file, ROOT, expected)
        print('Verified and installed ' + asset['name'], flush=True)
    for rel, h in expected.items():
        if digest(ROOT / rel) != h:
            raise RuntimeError('Incomplete dependency set: ' + rel)
    print('Verified %d external dependency artifacts.' % len(expected))

if __name__ == '__main__':
    main()
