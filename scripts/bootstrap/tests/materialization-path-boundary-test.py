import importlib.util
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location('boundary',
    Path(__file__).parents[1] / 'materialization-path-boundary.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class BoundaryTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.parent = Path(self.temp.name)
        self.root = self.parent / 'root with spaces'
        self.root.mkdir()
        self.boundary = module.MaterializationBoundary(self.root)

    def test_nested_unicode_missing_and_normalized_paths_match_baseline(self):
        for relative in ('src/compiler/file.spl', "src/한글/a'b.spl",
                         'src/../test/spec.spl', 'missing/deep/file'):
            path = self.root / relative
            self.assertEqual(self.boundary.contains(path),
                             path.resolve().is_relative_to(self.root.resolve()))
        self.boundary.verify_root()

    def test_parent_and_prefix_sibling_escapes_rejected(self):
        for path in (self.root / '../escape', self.parent / 'root with spaces-other/file'):
            self.assertFalse(self.boundary.contains(path))

    def test_root_replacement_rejected(self):
        self.root.rename(self.parent / 'old-root')
        self.root.mkdir()
        with self.assertRaisesRegex(ValueError, 'root changed'):
            self.boundary.verify_root()

    def test_child_symlink_escape_rejected(self):
        outside = self.parent / 'outside'
        outside.mkdir()
        link = self.root / 'link'
        try:
            link.symlink_to(outside, target_is_directory=True)
        except OSError:
            if __import__('os').name != 'nt':
                raise
            import subprocess
            result = subprocess.run(['cmd.exe', '/d', '/c', 'mklink', '/J',
                str(link), str(outside)], capture_output=True)
            self.assertEqual(result.returncode, 0)
        self.assertFalse(self.boundary.contains(link / 'payload'))
        link.unlink() if link.is_symlink() else link.rmdir()


if __name__ == '__main__':
    unittest.main()
