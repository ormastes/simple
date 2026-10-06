import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

p = Path(__file__).resolve().parents[1] / 'phase1-whole-tests.py'
s = importlib.util.spec_from_file_location('phase1', p)
m = importlib.util.module_from_spec(s); s.loader.exec_module(m)

class StreamingTests(unittest.TestCase):
    def test_large_non_json_stream_keeps_only_summary(self):
        with tempfile.TemporaryDirectory() as d:
            path = Path(d)/'stdout'; path.write_bytes((b'log entry\n'*100000)+b'{"success":true}\n')
            self.assertEqual(list(m.read_summary_lines(path, 128)), ['{"success":true}\n'])

    def test_giant_unterminated_line_fails_closed(self):
        with tempfile.TemporaryDirectory() as d:
            path = Path(d)/'stdout'; path.write_bytes(b'x'*10000)
            with self.assertRaisesRegex(ValueError, 'bounded summary'):
                list(m.read_summary_lines(path, 128))

    def test_per_file_partition_and_abort(self):
        row=dict(path='one.spl',passed=1,failed=0,skipped=0,pending=0,error=None)
        spec=dict(files=[row],total_passed=1,total_failed=0,total_skipped=0,total_pending=0)
        doc=dict(files=[],passed=0,failed=0,skipped=0,errors=0,total=0)
        result=dict(success=True,spec=spec,spl_doctest=doc,sdoctest=doc)
        self.assertEqual(m.validate_partitions(result),'')
        row['error']='TIMEOUT'
        self.assertIn('aborted',m.validate_partitions(result))
        row['error']=None;spec['total_passed']=2
        self.assertIn('disagree',m.validate_partitions(result))

if __name__=='__main__':unittest.main()
