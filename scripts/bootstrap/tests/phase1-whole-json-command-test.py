"""Exercise callback dispatch using the direct seed runner's diagnostic text mode.

This models the CLI boundary, not execution of Simple assertions.
"""
import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location(
    'phase1_callback', Path(__file__).parents[1] / 'phase1-whole-tests.py')
callback = importlib.util.module_from_spec(spec)
spec.loader.exec_module(callback)


class DispatchTests(unittest.TestCase):
    def exercise(self, failed):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            seed = root / 'seed.exe'
            seed.write_bytes(b'callback-boundary-fixture')
            for name in ('config/simple.test.sdn', 'config/sdoctest.sdn',
                         'src/app/test_runner_new/main.spl',
                         'src/app/test_runner_new/test_runner_main.spl',
                         'src/app/test_daemon/light_protocol.spl',
                         'src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl',
                         'src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl',
                         'src/lib/nogc_sync_mut/spec.spl',
                         'src/lib/nogc_sync_mut/test_runner/test_runner_output.spl',
                         'src/lib/nogc_sync_mut/test_runner/sdoctest/runner.spl',
                         'src/lib/nogc_sync_mut/test_runner/test_runner_files.spl',
                         'src/lib/nogc_sync_mut/test_runner/test_runner_args.spl',
                         'src/lib/nogc_sync_mut/test_runner/test_runner_types.spl',
                         'src/lib/nogc_sync_mut/test_runner/test_runner_async.spl',
                         'src/lib/nogc_sync_mut/test_runner/worker_memory.spl',
                         'src/lib/common/convert.spl'):
                target = root / name
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_text('fixture input', encoding='utf-8')
            def runner(command, **kwargs):
                self.assertIn('--format=text', command)
                self.assertNotIn('--json', command)
                report = (
                    'SPEC FILE VERDICT: one_spec.spl outcome=OK declared>=1 executed=1 passed=1 failed=0 skipped=0 dropped=0\n'
                    'Files: 1 discovered, 1 executed\n'
                    'Results: 1 total, 1 passed, 0 failed\n'
                    f'SPL Doctest: {0 if failed else 1} passed, {int(failed)} failed, 0 skipped\n'
                    f'SDoctest Results: 1 total, {0 if failed else 1} passed, {int(failed)} failed, 0 skipped, 0 errors\n'
                )
                kwargs['stdout'].write(report.encode())
                return SimpleNamespace(returncode=int(failed))

            output = root / 'output'
            argv = ['callback', '--seed', str(seed), '--seed-sha256',
                    hashlib.sha256(seed.read_bytes()).hexdigest(),
                    '--source-root', str(root), '--output-root', str(output)]
            with patch('sys.argv', argv), patch.object(callback.subprocess, 'run', runner):
                code = callback.main()
            receipt = json.loads((output / 'result.json').read_text())
            self.assertEqual(code, int(failed))
            self.assertEqual(receipt['status'], 'FAIL' if failed else 'PASS')
            categories = receipt['runner_summary']['categories']
            self.assertEqual(categories['spec']['passed'], 1)
            self.assertEqual(categories['spl_doctest']['failed'], int(failed))
            self.assertEqual(categories['sdoctest']['failed'], int(failed))
            self.assertTrue(receipt['coverage_status'].startswith('NOT_PROVEN'))

    def test_combined_categories_survive_direct_seed_dispatch(self):
        self.exercise(False)

    def test_failed_doctests_remain_failures(self):
        self.exercise(True)


if __name__ == '__main__':
    unittest.main()
