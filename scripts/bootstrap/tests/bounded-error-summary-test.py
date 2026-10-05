#!/usr/bin/env python3
import hashlib
import importlib.util
import json
import tempfile
import tracemalloc
import unittest
from pathlib import Path

spec = importlib.util.spec_from_file_location('summary', Path(__file__).parents[1] / 'bounded-error-summary.py')
summary = importlib.util.module_from_spec(spec)
spec.loader.exec_module(summary)


class SummaryTests(unittest.TestCase):
    def test_link_line_start_across_chunk_boundary(self):
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / 'log'
            path.write_bytes(b'x' * (summary.CHUNK - 5) + b'\nLinking: app\n')
            self.assertTrue(summary.summarize(path)['link_reached'])
            path.write_bytes(b'x' * (summary.CHUNK - 256) + b'Linked: embedded' + b'x' * summary.CHUNK)
            self.assertFalse(summary.summarize(path)['link_reached'])

    def test_large_unterminated_error_is_bounded(self):
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / 'log'
            digest = hashlib.sha256()
            with path.open('wb') as f:
                for chunk in [b'error: '] + [b'x' * 65536] * 1024 + [b' access violation 0xC0000005']:
                    f.write(chunk)
                    digest.update(chunk)
            tracemalloc.start()
            result = summary.summarize(path)
            _, peak = tracemalloc.get_traced_memory()
            tracemalloc.stop()
            self.assertLess(peak, 2 * 1024 * 1024)
            self.assertLess(len(json.dumps(result)), 4096)
            self.assertEqual(result['log_sha256'], digest.hexdigest())
            self.assertEqual(result['log_bytes'], path.stat().st_size)
            self.assertTrue(result['native_access_violation'])
            self.assertEqual(result['truncated_error_lines'], 1)
            self.assertIn('0xC0000005', result['error_lines'][0])

    def test_boundary_markers_and_last_phase(self):
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / 'log'
            path.write_bytes(b'x' * (summary.CHUNK - 8) + b'[build] phase=monomorphize\n'
                             b'prefix undefined reference\n[build] phase=codegen\nerror: final\n')
            result = summary.summarize(path)
            self.assertEqual(result['last_reported_phase'], 'codegen')
            self.assertTrue(result['link_reached'])
            self.assertEqual(result['error_lines'], ['error: final'])

    def test_error_marker_beyond_retained_head(self):
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / 'log'
            path.write_bytes(b'x' * (summary.CHUNK - 3) + b'error:' + b'y' * summary.CHUNK)
            result = summary.summarize(path)
            self.assertEqual(len(result['error_lines']), 1)
            self.assertTrue(result['error_locations'][0]['truncated'])

    def test_last_errors_and_offsets(self):
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / 'log'
            data = b'clean\n' + b''.join(('error: %02d\n' % n).encode() for n in range(30))
            path.write_bytes(data)
            result = summary.summarize(path)
            self.assertEqual(len(result['error_lines']), 16)
            self.assertEqual(result['error_lines'][0], 'error: 14')
            self.assertEqual(result['error_locations'][0]['offset'], data.index(b'error: 14'))

    def test_empty_and_invalid_utf8(self):
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / 'log'
            path.write_bytes(b'')
            self.assertEqual(summary.summarize(path)['error_lines'], [])
            path.write_bytes(b'error: \xff\r\nLinked: example\r\n')
            result = summary.summarize(path)
            self.assertTrue(result['link_reached'])
            self.assertIn('\ufffd', result['error_lines'][0])


if __name__ == '__main__':
    unittest.main()
