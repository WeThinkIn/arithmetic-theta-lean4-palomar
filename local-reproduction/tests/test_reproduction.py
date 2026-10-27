import hashlib
import importlib.util
from pathlib import Path
import tempfile
import unittest
import zipfile
from unittest import mock

SCRIPTS = Path(__file__).resolve().parents[1] / 'scripts'
def load(name):
    spec = importlib.util.spec_from_file_location(name, SCRIPTS / (name + '.py'))
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m

fetch = load('fetch_dependencies')
reproduce = load('reproduce')

class ReproductionTests(unittest.TestCase):
    def test_extract_and_detect_existing_corruption(self):
        with tempfile.TemporaryDirectory() as t:
            root = Path(t); archive = root / 'asset.zip'; rel = 'dependencies/lib/lean/Test.olean'
            with zipfile.ZipFile(archive, 'w') as z:z.writestr(rel, b'expected')
            expected = {rel: hashlib.sha256(b'expected').hexdigest()}
            fetch.unpack(archive, root, expected)
            self.assertEqual((root / rel).read_bytes(), b'expected')
            (root / rel).write_bytes(b'corrupted')
            with self.assertRaisesRegex(RuntimeError, 'refusing to overwrite'):fetch.unpack(archive, root, expected)
    def test_reject_unknown_and_traversal(self):
        with tempfile.TemporaryDirectory() as t:
            root = Path(t); archive = root / 'asset.zip'
            with zipfile.ZipFile(archive, 'w') as z:z.writestr('../escape', b'bad')
            with self.assertRaisesRegex(RuntimeError, 'Unexpected'):fetch.unpack(archive, root, {})
            self.assertFalse((root.parent / 'escape').exists())
    def test_reject_bad_content(self):
        with tempfile.TemporaryDirectory() as t:
            root = Path(t); archive = root / 'asset.zip'; rel = 'dependencies/lib/lean/Test.olean'
            with zipfile.ZipFile(archive, 'w') as z:z.writestr(rel, b'bad')
            with self.assertRaisesRegex(RuntimeError, 'checksum'):fetch.unpack(archive, root, {rel: '0' * 64})
            self.assertFalse((root / rel).exists())
    def test_wrong_toolchain(self):
        with mock.patch.object(reproduce.subprocess, 'check_output', return_value='Lean (version 4.35.0-rc2, x86_64)'):
            with self.assertRaisesRegex(RuntimeError, 'Expected Lean 4.33.1'):reproduce.resolve_lean('/tmp/lean')

if __name__ == '__main__':unittest.main()
