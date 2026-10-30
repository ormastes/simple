"""Bounded diagnostic report handling; these checks do not execute Simple tests."""
import importlib.util
from pathlib import Path
import tempfile
import unittest

p = Path(__file__).resolve().parents[1] / 'phase1-whole-tests.py'
s = importlib.util.spec_from_file_location('phase1', p)
m = importlib.util.module_from_spec(s)
s.loader.exec_module(m)


class StreamingTests(unittest.TestCase):
    def test_large_report_preserves_raw_diagnostic_lines(self):
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / 'stdout'
            report = 'log entry\n' * 100000 + 'Results: 1 total, 1 passed, 0 failed\n'
            path.write_text(report, encoding='utf-8')
            self.assertEqual(m.read_report(path), report)

    def test_report_size_limit_fails_closed(self):
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / 'stdout'
            path.write_bytes(b'x' * 129)
            with self.assertRaisesRegex(ValueError, 'bounded report size'):
                m.read_report(path, 128)

    def test_giant_unterminated_line_fails_closed(self):
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / 'stdout'
            path.write_bytes(b'x' * (m.MAX_LINE_BYTES + 1))
            with self.assertRaisesRegex(ValueError, 'bounded line size'):
                m.read_report(path)

    def test_invalid_utf8_is_not_silently_replaced(self):
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / 'stdout'
            path.write_bytes(b'\xff\n')
            with self.assertRaises(UnicodeError):
                m.read_report(path)


if __name__ == '__main__':
    unittest.main()
