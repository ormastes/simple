"""Evidence parser tests; never execute a compiler or claim product qualification."""
import importlib.util
import pathlib
import shutil
import os
import subprocess
import tempfile
import unittest

HELPER = pathlib.Path(__file__).parents[2] / 'check/lib/bootstrap-stage3/sanity-base-controls.py'
spec = importlib.util.spec_from_file_location('controls', HELPER)
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
HISTORY = pathlib.Path('C:/Users/user/.simple/worktrees/simple-windows-phase2/build/native_probe/llvm-patched-candidate-qualification1')
OWNER = pathlib.Path('C:/Users/user/.simple/worktrees/simple/runtime/llvm-patched-candidate-qualification')
CANDIDATE = pathlib.Path('C:/Users/user/.simple/worktrees/simple-windows-phase2/build/native_probe/llvm-patched-native-46557-attempt2/stage2-resume.uAm9eH/stage2/x86_64-pc-windows-msvc/simple.exe')

class ControlTests(unittest.TestCase):
    @unittest.skipUnless(os.name=='nt','Windows composed-authority junction case')
    def test_composed_receipt_junction_guard(self):
        with tempfile.TemporaryDirectory() as owned:
            root=pathlib.Path(owned).absolute(); external=root/'external';external.mkdir()
            receipt=external/'composed.env';receipt.write_text('schema=external-sentinel\n')
            junction=root/'junction'
            result=subprocess.run(['cmd.exe','/c','mklink','/J',str(junction),str(external)],capture_output=True,text=True,timeout=10)
            self.assertEqual(result.returncode,0,result.stderr)
            try:
                with self.assertRaisesRegex(ValueError,'proof authority reparse point'):
                    m.composition_records(junction/'composed.env')
                self.assertEqual(receipt.read_text(),'schema=external-sentinel\n')
            finally:
                os.rmdir(junction)
    def test_composition_guards(self):
        # Synthetic envelope only: the shell API separately requires every
        # real frontend collector, artifact and execution-output criterion.
        fresh = {'schema':'simple-bootstrap-sanity-evidence-v1','status':'pass',
            'base_control_profile':m.PROFILE,'base_control_writer_sha256':m.FRESH_WRITER,
            'base_control_snapshot_sha256':'controls',
            'candidate_sha256_before':m.CANDIDATE,'candidate_sha256_after':m.CANDIDATE,
            'frontend_smoke_status':'0','frontend_smoke_bootstrap1_ran':'true',
            'frontend_smoke_bootstrap_mode_status':'0','frontend_smoke_bootstrap0_raw_status':'0',
            'frontend_smoke_bootstrap1_raw_status':'0'}
        composed = {'schema':m.COMPOSED_SCHEMA,'profile':m.PROFILE,'status':'pass',
            'candidate_sha256':m.CANDIDATE,'base_sanity_sha256':m.ARCHIVE['sanity.env'],
            'base_job_sha256':m.ARCHIVE['qualification.receipt.env'],
            'base_log_sha256':m.ARCHIVE['qualification.log'],
            'fresh_sanity_sha256':'fresh','control_snapshot_sha256':'controls'}
        m.verify_composition_fields(composed,fresh,'fresh','controls')
        for key,value,reason in [('schema','unknown','unknown composition schema'),
            ('profile','unknown','unknown composition profile'),('status','fail','composition status'),
            ('candidate_sha256','changed','composition candidate'),
            ('base_sanity_sha256','changed','composition base identity'),
            ('fresh_sanity_sha256','changed','fresh sanity digest'),
            ('control_snapshot_sha256','changed','composition control snapshot')]:
            changed=dict(composed);changed[key]=value
            with self.subTest(composed=key),self.assertRaisesRegex(ValueError,reason):
                m.verify_composition_fields(changed,fresh,'fresh','controls')
        for key,value,reason in [('status','fail','fresh aggregate status'),
            ('base_control_profile','unknown','fresh control provenance'),
            ('base_control_writer_sha256','changed','fresh control writer'),
            ('base_control_snapshot_sha256','changed','fresh control snapshot'),
            ('candidate_sha256_after','changed','fresh full criterion'),
            ('frontend_smoke_bootstrap0_raw_status','124','fresh full criterion'),
            ('frontend_smoke_bootstrap1_ran','false','fresh full criterion'),
            ('frontend_smoke_bootstrap1_raw_status','1','fresh full criterion')]:
            changed=dict(fresh);changed[key]=value
            with self.subTest(fresh=key),self.assertRaisesRegex(ValueError,reason):
                m.verify_composition_fields(composed,changed,'fresh','controls')

    def test_actual_writer_mutation(self):
        m.verify_actual_writer()
        with tempfile.TemporaryDirectory() as root:
            changed=pathlib.Path(root)/'writer.shs';changed.write_text('changed')
            with self.assertRaisesRegex(ValueError,'changed actual fresh writer'):
                m.verify_actual_writer(changed)

    def test_shell_dispatch_gates(self):
        bash = 'C:/Program Files/Git/bin/bash.exe' if os.name=='nt' else shutil.which('bash')
        self.assertTrue(bash)
        facade = HELPER.parent.parent/'bootstrap-stage3-provenance.shs'
        def shellpath(p):
            s=str(p.absolute()).replace('\\','/')
            return '/'+s[0].lower()+'/'+s[3:] if len(s)>2 and s[1:3]==':/' else s
        with tempfile.TemporaryDirectory() as root:
            root=pathlib.Path(root)
            for schema,profile,expected in [('unknown','',1),
                ('simple-bootstrap-sanity-evidence-v1',m.PROFILE,1),
                ('simple-bootstrap-sanity-evidence-v1','',42),
                ('simple-bootstrap-sanity-components-v1','',42)]:
                receipt=root/'sanity.env'
                receipt.write_text('schema='+schema+'\n'+('base_control_profile='+profile+'\n' if profile else ''))
                script='''set -eu
BOOTSTRAP_STAGE3_FACADE_PATH=$1
. "$1"
_bootstrap_stage3_verify_sanity_evidence_receipt_legacy() { return 42; }
printf 'DISPATCH-READY\\n'
if bootstrap_stage3_verify_sanity_evidence_receipt "$2" "$2" "$3" /missing /missing; then code=0; else code=$?; fi
printf 'DISPATCH-STATUS=%s\\n' "$code"
'''
                result=subprocess.run([bash,'--noprofile','--norc','-c',script,'--',shellpath(facade),shellpath(receipt),shellpath(root)],capture_output=True,text=True,timeout=20)
                self.assertEqual(result.returncode,0,result.stderr)
                self.assertIn('DISPATCH-READY',result.stdout)
                self.assertIn('DISPATCH-STATUS='+str(expected),result.stdout)

    @unittest.skipUnless(os.name=='nt','Windows junction case')
    def test_junction_parent_rejected(self):
        with tempfile.TemporaryDirectory() as owned:
            root=pathlib.Path(owned).absolute(); external=root/'external';external.mkdir()
            sentinel=external/'sentinel.txt';sentinel.write_text('retained')
            junction=root/'junction'
            result=subprocess.run(['cmd.exe','/c','mklink','/J',str(junction),str(external)],capture_output=True,text=True,timeout=10)
            self.assertEqual(result.returncode,0,result.stderr)
            try:
                with self.assertRaisesRegex(ValueError,'proof authority reparse point'):
                    m.digest(junction/'sentinel.txt')
                self.assertEqual(sentinel.read_text(),'retained')
            finally:
                os.rmdir(junction)  # unlink junction itself, never traverse it
    def test_duplicate_record_rejected(self):
        with tempfile.TemporaryDirectory() as root:
            p = pathlib.Path(root) / 'record.env'
            p.write_text('version_status=0\nversion_status=1\n')
            with self.assertRaisesRegex(ValueError, 'duplicate record'):
                m.records(p)

    def test_profile_and_control_fail_closed(self):
        with self.assertRaisesRegex(ValueError, 'unknown control profile'):
            m.verify('receipt-defined-profile', *([pathlib.Path('/missing')] * 7))
        # Field-level negatives independently exercise semantics beyond byte pins.
        sanity = { 'schema':'simple-bootstrap-sanity-evidence-v1','status':'fail',
            'candidate_sha256_before':m.CANDIDATE,'candidate_sha256_after':m.CANDIDATE,
            'version_status':'0','version_output':'simple-bootstrap 1.0.0-rc.1',
            'version_expected':'1.0.0-rc.1','version_expect_status':'0','version_match_status':'0',
            'unsupported_status':'1','unsupported_match_status':'0','sha_stable_status':'0',
            'unsupported_output_sha256':'373ffddd775f9bc524eb271bab164edcd7a51209a53058465cd0538c50c8d806',
            'frontend_smoke_status':'124'}
        for key, value in [('status','pass'),('version_status','1'),('version_output','wrong'),
                           ('unsupported_status','0'),('candidate_sha256_after','changed')]:
            changed = dict(sanity); changed[key] = value
            with self.subTest(key=key), self.assertRaisesRegex(ValueError, 'historical control: ' + key):
                m.controls(changed, {})

    @unittest.skipUnless(HISTORY.is_dir() and CANDIDATE.is_file(), 'Windows archived evidence unavailable')
    def test_actual_immutable_evidence_and_physical_negatives(self):
        args = [m.PROFILE, HISTORY, OWNER, CANDIDATE,
                HISTORY/'source-before.txt', HISTORY/'current-consumer-before.env',
                HISTORY/'runtime-before.txt', HISTORY/'tools-before.txt']
        actual = m.verify(*args)
        self.assertEqual(actual['historical_aggregate_status'], 'fail')
        self.assertEqual(actual['version_status'], '0')
        self.assertEqual(actual['unsupported_status'], '1')
        with tempfile.TemporaryDirectory() as root:
            root = pathlib.Path(root)
            wrong = root/'wrong.txt'; wrong.write_text('changed')
            for index, reason in [(3,'changed candidate'),(4,'current tuple: source'),
                                  (5,'current tuple: current'),(6,'current tuple: runtime'),
                                  (7,'current tuple: tools')]:
                changed = list(args); changed[index] = wrong
                with self.subTest(index=index), self.assertRaisesRegex(ValueError, reason):
                    m.verify(*changed)
            for role, names, argument, reason in [('archive',m.ARCHIVE,1,'archive identity'),
                                                  ('owner',m.OWNERS,2,'control owner')]:
                target = root/role; target.mkdir()
                source = HISTORY if role == 'archive' else OWNER
                for name in names: shutil.copyfile(source/name,target/name)
                altered = next(iter(names)); (target/altered).write_text('tampered')
                changed = list(args); changed[argument] = target
                with self.subTest(role=role), self.assertRaisesRegex(ValueError, reason):
                    m.verify(*changed)
            original_job = m.records(HISTORY/'qualification.receipt.env')
            original_sanity = m.records(HISTORY/'sanity.env')
            for key, value in [('status','aborted'),('native_exit_status','0'),
                               ('reason','timeout'),('helper_sha256','changed')]:
                changed = dict(original_job); changed[key] = value
                with self.subTest(job=key), self.assertRaisesRegex(ValueError, 'historical job: ' + key):
                    m.controls(original_sanity, changed)

if __name__ == '__main__':
    unittest.main(verbosity=2)
