"""Receipt parser tests only; synthetic ledgers are never native evidence."""
from pathlib import Path
import subprocess
import tempfile
import unittest

VERIFIER = Path(__file__).resolve().parents[1] / 'verify-product-first-case.pl'
A, B, H = 'a'*64, 'b'*64, 'c'*64


class FirstCaseTests(unittest.TestCase):
    def check(self, outcome='pass', process=0, callbacks=1, other=False, begin=True, watchdog_exit=None, mode='monitor', limit=None, quiet='1'):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            head=f'simple-subsystem-registry-v1\tllvm\tcompiler\t{H}\t{H}\nowner_begin\tone.spl\t{H}\n'
            declarations=f'declare\t{A}\t{H}\ndeclare\t{B}\t{H}\n'
            end='owner_end\tone.spl\t2\tok\n'
            trailer=lambda count:f'complete\tregistration_ok=1\ttest_callbacks_executed={count}\thook_callbacks_executed=0\n'
            (root/'enum').write_text(head+declarations+end+trailer(0), newline='\n')
            body=(f'begin\t{A}\n' if begin else '')+f'result\t{A}\t{outcome}\n'
            if other: body+=f'begin\t{B}\nresult\t{B}\tpass\n'
            (root/'run').write_text(head+declarations+body+end+trailer(callbacks), newline='\n')
            if limit is None: limit='unlimited' if mode=='monitor' else '1000'
            (root/'watch').write_text('status=complete\nquiescent='+quiet+'\nobserver_errors=0\nrss_cap_mode='+mode+'\nrss_cap_enforced='+('1' if mode=='enforce' else '0')+'\nrss_limit_kib='+limit+'\nexit_status='+str(process if watchdog_exit is None else watchdog_exit)+'\n', newline='\n')
            return subprocess.run(['perl',str(VERIFIER),str(root/'enum'),str(root/'run'),A,str(process),str(root/'watch'),'1000',mode],capture_output=True,text=True)

    def test_exact_one_real_callback_pass(self):
        r=self.check(); self.assertEqual(r.returncode,0,r.stderr)
        self.assertIn('executed=1',r.stdout); self.assertIn('full_suite_count_contribution=0',r.stdout)

    def test_real_failure_is_retained(self):
        r=self.check('fail',1); self.assertEqual(r.returncode,1,r.stderr)
        self.assertIn('status=FAIL',r.stdout)

    def test_skip_is_not_first_case_success(self):
        r=self.check('skip',0,0,begin=False); self.assertEqual(r.returncode,3,r.stderr)
        self.assertNotIn('status=PASS',r.stdout)

    def test_ignored_selector_rejected(self):
        self.assertNotEqual(self.check(callbacks=2,other=True).returncode,0)

    def test_crash_saved_pass_or_watchdog_mismatch_rejected(self):
        self.assertNotEqual(self.check(process=139).returncode,0)
        self.assertNotEqual(self.check(watchdog_exit=1).returncode,0)

    def test_pending_or_missing_callback_rejected(self):
        self.assertNotEqual(self.check('pending').returncode,0)
        self.assertNotEqual(self.check(callbacks=0).returncode,0)

    def test_real_monitor_and_enforced_limit_formats(self):
        self.assertEqual(self.check(mode='enforce').returncode,0)
        self.assertNotEqual(self.check(mode='enforce',limit='unlimited').returncode,0)
        self.assertNotEqual(self.check(limit='1000').returncode,0)

    def test_nonquiescent_tree_cannot_pass(self):
        self.assertNotEqual(self.check(quiet='0').returncode,0)


if __name__=='__main__':unittest.main()
