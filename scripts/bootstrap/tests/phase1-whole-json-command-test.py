"""Exercise callback dispatch using the direct seed runner's public JSON mode.

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
                         'src/lib/nogc_sync_mut/test_runner/test_runner_files.spl'):
                target = root / name
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_text('fixture input', encoding='utf-8')
            spec_row = dict(path='one_spec.spl', passed=1, failed=0,
                            skipped=0, pending=0, error=None)
            spec_result = dict(success=True, files=[spec_row], total_passed=1,
                               total_failed=0, total_skipped=0, total_pending=0)
            doc_row = dict(path='one.md', passed=0 if failed else 1,
                           failed=int(failed), skipped=0, errors=0)
            docs = dict(files=[doc_row], total=1, passed=doc_row['passed'],
                        failed=int(failed), skipped=0, errors=0)
            summary = dict(success=not failed, spec=spec_result,
                           spl_doctest=docs, sdoctest=docs)

            def runner(command, **kwargs):
                # Public direct dispatch recognizes --json or --format json.
                # --format=json only affects the spec formatter in the seed.
                json_mode = '--json' in command or any(
                    command[i:i+2] == ['--format', 'json']
                    for i in range(len(command)-1))
                kwargs['stdout'].write(json.dumps(
                    summary if json_mode else spec_result).encode() + b'\n')
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
            self.assertEqual(receipt['runner_summary'], summary)

    def test_combined_categories_survive_direct_seed_dispatch(self):
        self.exercise(False)

    def test_failed_doctests_remain_failures(self):
        self.exercise(True)


if __name__ == '__main__':
    unittest.main()
