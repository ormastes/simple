import unittest
import pathlib,sys
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parents[1]/"lib"))
from executable_batch_policy import *
C=dict(max_executables=20,headroom_bytes=16*GIB,minimum_estimate_bytes=GIB,rss_to_commit_safety_factor=2)
class AdmissionTests(unittest.TestCase):
 def test_group_never_more_than20(self):
  for active in range(20,40):self.assertFalse(may_start(active,[GIB]*100,10**15,C))
 def test_initial_one_and_observed_ramp(self):
  self.assertTrue(may_start(0,[],100*GIB,C));self.assertFalse(may_start(1,[],100*GIB,C));self.assertTrue(may_start(1,[GIB],100*GIB,C));self.assertFalse(may_start(2,[GIB],100*GIB,C))
 def test_memory_pressure_queues_without_mutation(self):
  active=[1,2,3];before=active.copy();self.assertFalse(may_start(len(active),[8*GIB]*8,20*GIB,C));self.assertEqual(active,before)
 def test_failure_continues_only_after_closure(self):
  good=dict(quiescent='1',observer_errors='0',status='complete')
  self.assertEqual(outcome(1,dict(compile_exit=1),[good]),'CONTINUE');self.assertEqual(outcome(139,dict(compile_exit=139),[good]),'CONTINUE')
  self.assertEqual(outcome(139,None,[]),'BLOCKED_UNVERIFIED_CHILD');self.assertEqual(outcome(1,dict(compile_exit=1),[dict(good,quiescent='0')]),'BLOCKED_UNVERIFIED_CHILD')
 def test_lease_cleanup_requires_quiescence(self):
  self.assertFalse(closed_rss(dict(status='complete',quiescent='0',observer_errors='0')));self.assertFalse(closed_rss(dict(status='complete',quiescent='1',observer_errors='1')))
 def test_nonzero_child_cannot_claim_success(self):
  good=dict(quiescent='1',observer_errors='0',status='complete')
  self.assertEqual(outcome(1,dict(compile_exit=0,terminal_status='LINKED_SANITY_PASS',sanity_pass=True),[good]),'BLOCKED_CHILD_RESULT_MISMATCH')
 def test_resume_exact_identity_and_sanity(self):
  t=dict(producer_sha256='p',source='s',backend='cranelift',entry='main.spl',options={'threads':1});saved=dict(identity=identity(t),binary_sha256='b',binary_linked=True,sanity_pass=True,closure='CLOSED')
  self.assertTrue(reusable_success(saved,t,'b'));self.assertFalse(reusable_success(saved,dict(t,source='changed'),'b'));self.assertFalse(reusable_success(saved,t,'changed'));self.assertFalse(reusable_success(dict(saved,sanity_pass=False),t,'b'))
if __name__=='__main__':unittest.main()
