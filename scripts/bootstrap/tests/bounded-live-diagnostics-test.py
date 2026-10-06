import hashlib
import importlib.util
import json
import pathlib
import subprocess
import sys
import tempfile
import threading
import time
import tracemalloc
import types
import unittest
from unittest import mock

ROOT=pathlib.Path(__file__).resolve().parents[1]
def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    value=importlib.util.module_from_spec(spec);spec.loader.exec_module(value);return value
M=module('diagnostic_subject',ROOT/'bounded-error-summary.py')
A=module('adapter_subject',ROOT/'bounded-stream-live-adapter.py')

class DiagnosticsTests(unittest.TestCase):
    def test_triage_consumes_only_bound_summary_and_reports_truncation(self):
        with tempfile.TemporaryDirectory() as temp:
            t=pathlib.Path(temp);s=M.DiagnosticStreamSummary(max_events=1,event_bytes=64)
            s.feed(b'[hir-fatal] first\n[hir-fatal] '+b'x'*200)
            summary=s.finish();data=json.dumps(summary).encode();p=t/'diagnostics.json';p.write_bytes(data)
            receipt=dict(diagnostic_summary_path=str(p),diagnostic_summary_sha256=hashlib.sha256(data).hexdigest(),stream_sha256=summary['stream_sha256'],bytes_seen=summary['stream_bytes'])
            (t/'stream.json').write_text(json.dumps(receipt))
            row=A.diagnostic_evidence(t)
            self.assertEqual(row['retained_markers'],{'[hir-fatal]':1})
            self.assertEqual(row['observed_markers'],{'[hir-fatal]':2})
            self.assertEqual(row['events_dropped'],1);self.assertEqual(row['truncated_events'],1)
            self.assertTrue(row['excerpts'][0]['truncated'])
            p.write_bytes(data+b' ')
            with self.assertRaises(AssertionError):A.diagnostic_evidence(t)

    def test_sparse_output_is_visible_before_child_eof(self):
        class Retention:
            def __init__(self,stream,cap,mode):
                self.stream=stream;self.observed=self.head_bytes=self.tail_bytes=0
                self.stream_hash=hashlib.sha256();self.log_hash=hashlib.sha256()
            def feed(self,block):
                self.observed+=len(block);self.head_bytes+=len(block)
                self.stream_hash.update(block);self.log_hash.update(block);self.stream.write(block)
            def finish(self):pass
        class Observer:
            calls=0
            def __init__(self,output,*args):self.output=output;self.error=None
            def feed(self,block):
                Observer.calls+=1
                (self.output/'visible-progress').write_bytes(block)
            def publish(self,*args,**kwargs):pass
        with tempfile.TemporaryDirectory() as temp:
            t=pathlib.Path(temp);release=t/'release';errors=[];result=[]
            code="import sys,time,pathlib; print('sparse progress',flush=True); p=pathlib.Path(sys.argv[1]); deadline=time.monotonic()+8\nwhile not p.exists() and time.monotonic()<deadline: time.sleep(.01)\nsys.exit(0 if p.exists() else 9)"
            def run():
                try:result.append(A.run_bounded([sys.executable,'-c',code,str(release)],t/'out','logger','pin',summary_path='summary',summary_sha='pin'))
                except Exception as error:errors.append(error)
            loader=lambda path,digest: M if str(path)=='summary' else types.SimpleNamespace(BoundedLog=Retention,LiveLogObserver=Observer)
            with mock.patch.object(A,'load_logger',loader):
                worker=threading.Thread(target=run);worker.start()
                try:
                    deadline=time.monotonic()+5
                    while not (t/'out/visible-progress').exists() and time.monotonic()<deadline:time.sleep(.02)
                    self.assertTrue((t/'out/visible-progress').exists(),'Sparse output blocked until EOF')
                    self.assertTrue(worker.is_alive(),'Child must still be waiting for release')
                    self.assertIn(b'sparse progress',(t/'out/retained.log').read_bytes())
                    self.assertLessEqual(Observer.calls,2,'Chunk reads, not per-byte callbacks')
                finally:release.touch();worker.join(10)
            self.assertFalse(worker.is_alive());self.assertEqual(errors,[]);self.assertEqual(result,[0])

    def test_middle_fatal_survives_oversized_output(self):
        s=M.DiagnosticStreamSummary();block=b'x'*65536
        for _ in range(80):s.feed(block)
        s.feed(b'[hir-fatal] path=src/app/bad.spl text=real failure[BOOTSTRAP-PHASE] next')
        for _ in range(80):s.feed(block)
        result=s.finish()
        self.assertEqual(result['events_observed'],1)
        self.assertIn('src/app/bad.spl',result['records'][0]['text'])
        self.assertEqual(result['records'][0]['offset'],80*65536)

    def test_all_marker_splits_and_unterminated_final_event(self):
        data=b'prefix[hir-fatal] path=owner.spl text=bad[BOOTSTRAP-PHASE]ok\nerror: final'
        for split in range(len(data)+1):
            s=M.DiagnosticStreamSummary();s.feed(data[:split]);s.feed(data[split:]);r=s.finish()
            self.assertEqual([x['marker'] for x in r['records']],['[hir-fatal]','error:'])
            self.assertEqual(r['stream_sha256'],hashlib.sha256(data).hexdigest())
            self.assertEqual(r['records'][1]['text'],'error: final')

    def test_bounded_counts_and_truncation(self):
        s=M.DiagnosticStreamSummary(max_events=2,event_bytes=64)
        for _ in range(5):s.feed(b'[hir-fatal] '+b'a'*200+b'\n')
        r=s.finish()
        self.assertEqual((r['events_observed'],r['events_retained'],r['events_dropped'],r['truncated_events']),(5,2,3,5))
        self.assertTrue(all(x['truncated'] and len(x['text'])==64 for x in r['records']))

    def test_huge_single_event_has_bounded_working_memory(self):
        block=b'x'*65536
        tracemalloc.start()
        s=M.DiagnosticStreamSummary();s.feed(b'[hir-fatal] ')
        for _ in range(1024):s.feed(block)
        r=s.finish();_,peak=tracemalloc.get_traced_memory();tracemalloc.stop()
        self.assertLess(peak,2*1024*1024)
        self.assertEqual(r['events_observed'],1)
        self.assertTrue(r['records'][0]['truncated'])
        self.assertGreater(r['records'][0]['bytes'],64*1024*1024)

    def test_phase_and_reexport_warning_are_not_fatal_events(self):
        s=M.DiagnosticStreamSummary()
        s.feed(b'[BOOTSTRAP-PHASE] error_codes.spl[hir-reexport-chase-unresolved] a warning\n[build] failed=0')
        self.assertEqual(s.finish()['events_observed'],0)

    def test_untrusted_helper_rejected_before_execution(self):
        with tempfile.TemporaryDirectory() as temp:
            p=pathlib.Path(temp)/'bad.py';sentinel=pathlib.Path(temp)/'executed'
            p.write_text('from pathlib import Path\nPath('+repr(str(sentinel))+').touch()\n')
            with self.assertRaises(RuntimeError):A.load_logger(p,'0'*64)
            self.assertFalse(sentinel.exists())

    def test_adapter_captures_middle_error_and_preserves_nonzero_exit(self):
        # Test double only for previously reviewed log retention/observer APIs.
        # A real subprocess supplies the bytes and exit code under test.
        logger_source='''import hashlib
class BoundedLog:
 def __init__(self,f,cap,mode):
  self.f=f;self.cap=cap;self.observed=0;self.head_bytes=0;self.tail_bytes=0;self.stream_hash=hashlib.sha256();self.log_hash=hashlib.sha256()
 def feed(self,b):
  self.observed+=len(b);self.stream_hash.update(b);keep=b[:max(0,self.cap-self.head_bytes)];self.f.write(keep);self.log_hash.update(keep);self.head_bytes+=len(keep)
 def finish(self):pass
class LiveLogObserver:
 def __init__(self,*args):self.error=None
 def feed(self,b):pass
 def publish(self,*args,**kwargs):pass
'''
        with tempfile.TemporaryDirectory() as temp:
            t=pathlib.Path(temp);logger=t/'logger.py';logger.write_text(logger_source)
            command=[sys.executable,'-c',"import sys;w=sys.stdout.buffer.write;w(b'x'*200000);w(b'\\n[hir-fatal] actual middle failure\\n');w(b'z'*200000);sys.exit(7)"]
            code=A.run_bounded(command,t/'out',logger,hashlib.sha256(logger.read_bytes()).hexdigest(),cap=1024,
                summary_path=ROOT/'bounded-error-summary.py',summary_sha=hashlib.sha256((ROOT/'bounded-error-summary.py').read_bytes()).hexdigest())
            self.assertEqual(code,7)
            self.assertNotIn(b'actual middle failure',(t/'out/retained.log').read_bytes())
            r=json.loads((t/'out/diagnostics.json').read_text());receipt=json.loads((t/'out/stream.json').read_text())
            self.assertEqual(r['events_observed'],1)
            self.assertIn('actual middle failure',r['records'][0]['text'])
            self.assertEqual(receipt['exit_code'],7)
            self.assertEqual(receipt['stream_sha256'],r['stream_sha256'])
            self.assertTrue(receipt['output_complete'])


    def test_exact_full_stream_marker_counts_survive_tail_eviction(self):
        s=M.DiagnosticStreamSummary(max_events=2,event_bytes=64)
        for _ in range(1000):s.feed(b'error: writer lock busy\n')
        s.feed(b'[hir-fatal] different failure\n[FAIL] final\n')
        r=s.finish()
        self.assertEqual(r['marker_counts'],{'error:':1000,'[hir-fatal]':1,'[fail]':1})
        self.assertEqual(r['events_observed'],1002)
        self.assertEqual(r['representative_samples'][0]['occurrences'],1000)
        self.assertEqual(r['sample_overflow_events'],1)
        self.assertFalse(r['cause_inventory_complete'])

    def test_bracketed_error_marker_at_every_chunk_split(self):
        data=b'prefix error[E1002]: real error\n[ERROR] native failure'
        for split in range(len(data)+1):
            s=M.DiagnosticStreamSummary();s.feed(data[:split]);s.feed(data[split:]);r=s.finish()
            self.assertEqual(r['marker_counts'],{'error[code]:':1,'[error]':1})
            self.assertEqual(r['events_observed'],2)

    def test_full_event_fingerprint_distinguishes_identical_clipped_prefix(self):
        s=M.DiagnosticStreamSummary(max_events=2,event_bytes=64)
        prefix=b'error: '+b'x'*10000
        s.feed(prefix+b'A\n'+prefix+b'B\n'+prefix+b'A\n')
        r=s.finish();samples=r['representative_samples']
        self.assertEqual([x['occurrences'] for x in samples],[2,1])
        self.assertEqual(samples[0]['text'],samples[1]['text'])
        self.assertNotEqual(samples[0]['event_sha256'],samples[1]['event_sha256'])
        self.assertEqual(r['sample_overflow_events'],0)

    def test_many_unique_events_have_bounded_samples_and_exact_overflow(self):
        tracemalloc.start();s=M.DiagnosticStreamSummary()
        for i in range(20000):s.feed(('error: unique failure '+str(i)+'\n').encode())
        # Revisit a retained fingerprint after saturation: its count stays exact.
        s.feed(b'error: unique failure 0\n');r=s.finish()
        _,peak=tracemalloc.get_traced_memory();tracemalloc.stop()
        self.assertLess(peak,2*1024*1024)
        self.assertEqual(r['marker_counts'],{'error:':20001})
        self.assertEqual(len(r['representative_samples']),16)
        self.assertEqual(r['representative_samples'][0]['occurrences'],2)
        self.assertEqual(r['sample_overflow_events'],20000-16)
        self.assertEqual(sum(x['occurrences'] for x in r['representative_samples'])+r['sample_overflow_events'],20001)
        self.assertEqual(r['events_dropped'],20001-64)

    def test_default_summary_stays_within_reader_limit_for_escaped_text(self):
        s=M.DiagnosticStreamSummary()
        for i in range(100):s.feed(b'error: '+str(i).encode()+b'\0'*1024+b'\n')
        self.assertLessEqual(len(json.dumps(s.finish()).encode()),512*1024)

if __name__=='__main__':unittest.main()
