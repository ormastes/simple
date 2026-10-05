"""Bounded-memory regression; paths are consumed, never retained."""
import importlib.util
from pathlib import Path
import tempfile
import tracemalloc
import unittest

spec = importlib.util.spec_from_file_location('boundary',
    Path(__file__).parents[1] / 'materialization-path-boundary.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class MemoryTests(unittest.TestCase):
    def test_streaming_paths_have_bounded_live_memory(self):
        with tempfile.TemporaryDirectory() as directory:
            boundary = module.MaterializationBoundary(directory)
            tracemalloc.start()
            try:
                for index in range(10000):
                    self.assertTrue(boundary.contains(Path(directory) / f'file-{index}.spl'))
                current, peak = tracemalloc.get_traced_memory()
            finally:
                tracemalloc.stop()
            boundary.verify_root()
            # pathlib interns path components in CPython's process-wide table.
            # Include that real cost rather than attributing it to this helper.
            self.assertEqual(set(vars(boundary)), {'root', 'resolved_root', 'identity'})
            self.assertLess(current, 2 * 1024 * 1024)
            self.assertLess(peak, 2 * 1024 * 1024)
            print(f'paths=10000 traced_current={current} traced_peak={peak}')


if __name__ == '__main__':
    unittest.main()
