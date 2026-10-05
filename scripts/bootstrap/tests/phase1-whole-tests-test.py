import importlib.util
import json
from pathlib import Path
import unittest

path = Path(__file__).resolve().parents[1] / 'phase1-whole-tests.py'
spec = importlib.util.spec_from_file_location('phase1', path)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class ReceiptTests(unittest.TestCase):
    def summary(self):
        return dict(success=True, spec=dict(success=True, total_passed=2, total_failed=0,
                    total_skipped=1, total_pending=0, files=[]),
                    spl_doctest=dict(passed=1, failed=0, skipped=3, errors=0),
                    sdoctest=dict(passed=1, failed=0, skipped=0, errors=0))

    def test_preserves_skips_separately(self):
        status, summary, _ = module.classify(0, json.dumps(self.summary()))
        self.assertEqual(status, 'PASS')
        self.assertEqual(summary['spl_doctest']['skipped'], 3)

    def test_crash_cannot_pass_saved_success(self):
        self.assertEqual(module.classify(139, json.dumps(self.summary()))[0], 'INFRASTRUCTURE_FAILED')

    def test_partial_or_duplicate_summary_rejected(self):
        value = json.dumps(self.summary())
        self.assertEqual(module.classify(0, value+'\n'+value)[0], 'INFRASTRUCTURE_FAILED')
        item = self.summary(); item['sdoctest'] = None
        self.assertEqual(module.classify(0, json.dumps(item))[0], 'INFRASTRUCTURE_FAILED')

    def test_failed_counts_override_success_flag(self):
        item = self.summary(); item['sdoctest']['failed'] = 1
        self.assertEqual(module.classify(0, json.dumps(item))[0], 'FAIL')

    def test_no_executed_assertions_or_bad_counters_rejected(self):
        item = self.summary(); item['spec']['total_passed'] = 0
        item['spl_doctest']['passed'] = item['sdoctest']['passed'] = 0
        self.assertEqual(module.classify(0, json.dumps(item))[0], 'INFRASTRUCTURE_FAILED')
        item = self.summary(); item['spec']['total_passed'] = True
        self.assertEqual(module.classify(0, json.dumps(item))[0], 'INFRASTRUCTURE_FAILED')


if __name__ == '__main__': unittest.main()
