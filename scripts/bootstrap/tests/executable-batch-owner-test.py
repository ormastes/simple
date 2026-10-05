import copy
import json
import os
import pathlib
import subprocess
import sys
import tempfile
import unittest
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / 'lib'))
from executable_batch_policy import validate_owned_ancestry, preflight_invocation

class OwnershipTests(unittest.TestCase):
    def setUp(self):
        self.config = dict(global_job_budget=80, admission_root='admission', parent_collector_receipt='cfec.env', collector=dict(path=str(pathlib.Path('collector.py').resolve()), sha256='helper'))
        self.launch = dict(owner_pid=10, collector_pid=20, threads=20, reservation='admission/lane.json', request='request.json', request_sha256='request')
        self.reservation = dict(owner_pid=10, owner_start_utc='2026-10-05T00:00:00Z', threads=20, schema='diagnostic-downstream-reservation/1', total_job_budget=80, receipt_path='cfec.env', helper_sha256='helper')
        self.request = dict(threads=20, command=['python', 'runner.py', '--packet', 'packet'], files={'config.json':'config'})
        self.rows = [dict(pid=30, parent_pid=20, start_utc='2026-10-05T00:00:02Z', command_line='python runner.py'), dict(pid=20, parent_pid=10, start_utc='2026-10-05T00:00:01Z', command_line='python collector.py --timeout-seconds 0 --root-exit-policy terminate-job'), dict(pid=10, parent_pid=1, start_utc='2026-10-05T00:00:00Z', command_line='owner')]
        self.rows[1]['command_line']='python \"'+self.config['collector']['path']+'\" --timeout-seconds 0 --root-exit-policy terminate-job'
    def validate(self, rows=None, request=None):
        def hashes(path):
            return {'request.json':'request', 'config.json':'config', 'collector.py':'helper'}[pathlib.Path(path).name]
        validate_owned_ancestry(self.config, self.launch, self.reservation, request or self.request, self.rows if rows is None else rows, 30, 'runner.py', 'packet', hashes)
    def test_valid_live_chain(self):
        self.validate()
    def test_stale_owner_rejected(self):
        with self.assertRaises(AssertionError):self.validate(self.rows[:2])
    def test_reused_owner_pid_rejected(self):
        rows=copy.deepcopy(self.rows);rows[2]['start_utc']='2026-10-05T00:00:03Z'
        with self.assertRaises(AssertionError):self.validate(rows)
    def test_unrelated_caller_rejected(self):
        rows=copy.deepcopy(self.rows);rows[0]['parent_pid']=10
        with self.assertRaises(AssertionError):self.validate(rows)
    def test_reused_collector_pid_rejected(self):
        rows=copy.deepcopy(self.rows);rows[1]['start_utc']='2026-10-05T00:00:03Z'
        with self.assertRaises(AssertionError):self.validate(rows)
    def test_wrong_collector_command_rejected(self):
        rows=copy.deepcopy(self.rows);rows[1]['command_line']='unrelated.py'
        with self.assertRaises(AssertionError):self.validate(rows)
    def test_unbound_runner_rejected(self):
        request=copy.deepcopy(self.request);request['command']=['python','unrelated.py']
        with self.assertRaises(AssertionError):self.validate(request=request)
    def test_real_preflight_inherits_same_cwd_and_environment(self):
        with tempfile.TemporaryDirectory() as directory:
            code='import os,pathlib;assert os.environ["BATCH_TEST_VALUE"]=="bound";assert pathlib.Path.cwd()==pathlib.Path(os.environ["BATCH_TEST_CWD"])'
            request=dict(command=[sys.executable,'-c',code],cwd=directory,environment={'BATCH_TEST_VALUE':'bound','BATCH_TEST_CWD':directory})
            command,cwd,env=preflight_invocation(request,os.environ)
            subprocess.run(command,cwd=cwd,env=env,check=True)
    @unittest.skipUnless(os.name=='nt' and os.environ.get('SIMPLE_BOOTSTRAP_POWERSHELL'), 'Windows observer requires configured PowerShell')
    def test_observes_actual_parent_chain(self):
        observer=pathlib.Path(__file__).resolve().parents[1]/'lib/executable-batch-processes.ps1'
        output=subprocess.check_output([os.environ['SIMPLE_BOOTSTRAP_POWERSHELL'],'-NoProfile','-File',str(observer),'-BatchProcessId',str(os.getpid()),'-OwnerProcessId',str(os.getppid())],text=True)
        rows=json.loads(output);self.assertEqual(rows[0]['pid'],os.getpid());self.assertEqual(rows[-1]['pid'],os.getppid());self.assertTrue(all(row['start_utc'] for row in rows))
    def test_empty_manifest_clear_error(self):
        with tempfile.TemporaryDirectory() as directory:
            root=pathlib.Path(directory);(root/'config.json').write_text('{}');(root/'tasks.json').write_text('{"targets":[]}')
            script=pathlib.Path(__file__).resolve().parents[1]/'adaptive-executable-batch.py'
            result=subprocess.run([sys.executable,str(script),'--packet',directory,'--preflight'],capture_output=True,text=True)
            self.assertNotEqual(result.returncode,0);self.assertIn('Empty target manifest',result.stderr)

if __name__=='__main__':unittest.main()
