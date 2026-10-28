import importlib.util
from pathlib import Path
import unittest

path = Path(__file__).resolve().parents[1] / 'phase1-whole-tests.py'
spec = importlib.util.spec_from_file_location('phase1', path)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

POSITIVE = '''SPEC FILE VERDICT: /fixtures/a.spec outcome=OK declared>=1 executed=1 passed=1 failed=0 skipped=0 dropped=0
Files:   1 discovered, 1 executed
Results: 1 total, 1 passed, 0 failed
SPL Doctest: 1 passed, 0 failed, 0 skipped
SDoctest Results: 1 total, 1 passed, 0 failed, 0 skipped, 0 errors'''
RED = POSITIVE.replace('outcome=OK declared>=1 executed=1 passed=1 failed=0', 'outcome=ERROR declared>=1 executed=1 passed=0 failed=1').replace('Results: 1 total, 1 passed, 0 failed', 'Results: 1 total, 0 passed, 1 failed').replace('SPL Doctest: 1 passed', 'SPL Doctest: 0 passed').replace('SDoctest Results: 1 total, 1 passed, 0 failed', 'SDoctest Results: 1 total, 0 passed, 1 failed')


class ReceiptTests(unittest.TestCase):
    def test_positive_and_ansi(self):
        status, report, _ = module.classify(0, POSITIVE.replace('✓', '\x1b[32m✓\x1b[0m'))
        self.assertEqual(status, 'PASS')
        self.assertEqual(report['categories']['spec']['passed'], 1)
        self.assertEqual(report['categories']['spl_doctest']['passed'], 1)
        self.assertEqual(report['file_summary']['discovered'], 1)

    def test_doctest_progress_banner_is_not_a_category_summary(self):
        report = POSITIVE.replace('SPL Doctest: 1 passed', 'SPL Doctest: Running doctests from 1 source file(s)...\nSPL Doctest: 1 passed')
        self.assertEqual(module.classify(0, report)[0], 'PASS')
        self.assertEqual(module.classify(0, report.replace('SPL Doctest: 1 passed, 0 failed, 0 skipped', ''))[0], 'INFRASTRUCTURE_FAILED')

    def test_red_requires_nonzero_and_failure_evidence(self):
        self.assertEqual(module.classify(1, RED)[0], 'FAIL')
        self.assertEqual(module.classify(0, RED)[0], 'INFRASTRUCTURE_FAILED')

    def test_zero_and_missing_duplicate_or_mismatched_summaries_fail_closed(self):
        zero = (POSITIVE.replace('executed=1 passed=1', 'executed=0 passed=0')
                .replace('Results: 1 total, 1 passed, 0 failed', 'Results: 0 total, 0 passed, 0 failed')
                .replace('SPL Doctest: 1 passed', 'SPL Doctest: 0 passed')
                .replace('SDoctest Results: 1 total, 1 passed', 'SDoctest Results: 0 total, 0 passed'))
        self.assertEqual(module.classify(0, zero)[0], 'INFRASTRUCTURE_FAILED')
        self.assertEqual(module.classify(0, POSITIVE + '\n' + POSITIVE)[0], 'INFRASTRUCTURE_FAILED')
        self.assertEqual(module.classify(0, POSITIVE.replace('SPL Doctest:', 'SPL Missing:'))[0], 'INFRASTRUCTURE_FAILED')
        self.assertEqual(module.classify(0, POSITIVE.replace('1 discovered, 1 executed', '2 discovered, 1 executed'))[0], 'INFRASTRUCTURE_FAILED')

    def test_crash_and_unverified_file_do_not_pass(self):
        self.assertEqual(module.classify(139, POSITIVE)[0], 'INFRASTRUCTURE_FAILED')
        dropped = POSITIVE.replace('dropped=0', 'dropped=1')
        self.assertEqual(module.classify(0, dropped)[0], 'INFRASTRUCTURE_FAILED')

    def test_malformed_summaries_and_unverified_suffixes_fail_closed(self):
        self.assertEqual(module.classify(0, POSITIVE.replace('Results: 1 total, 1 passed, 0 failed', 'Results: malformed'))[0], 'INFRASTRUCTURE_FAILED')
        self.assertEqual(module.classify(0, POSITIVE.replace('Results: 1 total, 1 passed, 0 failed', 'Results: 1 total, 1 passed, 0 failed, 1 timed out (unverified)'))[0], 'INFRASTRUCTURE_FAILED')
        self.assertEqual(module.classify(0, POSITIVE.replace('SDoctest Results:', 'SDoctest Results (fail-as-success):').replace('1 passed, 0 failed, 0 skipped', '1 passed, 0 failed, 0 accepted, 0 skipped'))[0], 'INFRASTRUCTURE_FAILED')

    def test_process_failure_stays_infrastructure_in_mixed_report(self):
        process_row = 'SPEC FILE VERDICT: /fixtures/process.spec outcome=ERROR declared>=1 executed=1 passed=1 failed=0 in_development=0 dropped=0 process_error=1 reason=child-exit-nonzero'
        mixed = RED.replace('Files:   1 discovered, 1 executed', process_row + '\nFiles:   2 discovered, 2 executed').replace('Results: 1 total, 0 passed, 1 failed', 'Results: 2 total, 1 passed, 1 failed')
        status, _, reason = module.classify(1, mixed)
        self.assertEqual(status, 'INFRASTRUCTURE_FAILED')
        self.assertIn('child process failed', reason)

    def test_declared_work_and_verdict_outcome_must_match(self):
        declared_more = POSITIVE.replace('declared>=1 executed=1', 'declared>=2 executed=1')
        self.assertEqual(module.classify(0, declared_more)[0], 'INFRASTRUCTURE_FAILED')
        contradictory = POSITIVE.replace('executed=1 passed=1 failed=0', 'executed=1 passed=0 failed=1')
        self.assertEqual(module.classify(0, contradictory)[0], 'INFRASTRUCTURE_FAILED')
        degraded = POSITIVE.replace('dropped=0', 'dropped=0 degraded=mcdc-obligation-manifest-absent')
        status, report, _ = module.classify(0, degraded)
        self.assertEqual(status, 'PASS')
        self.assertTrue(report['spec_files'][0]['degraded'])


if __name__ == '__main__':
    unittest.main()
