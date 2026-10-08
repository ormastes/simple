"""Host callback contract tests; mock child is not native test evidence."""
import contextlib
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

path = Path(__file__).resolve().parents[1] / 'phase1-whole-tests.py'
spec = importlib.util.spec_from_file_location('phase1_jobs', path)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class JobsTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.seed = self.root / 'seed.exe'
        self.seed.write_bytes(b'host-test-placeholder-never-executed')
        self.source = self.root / 'source'
        for name in ('config/simple.test.sdn', 'config/sdoctest.sdn',
                     'src/app/test_runner_new/main.spl',
                     'src/app/test_runner_new/test_runner_main.spl',
                     'src/lib/nogc_sync_mut/test_runner/test_runner_files.spl',
              'src/lib/nogc_sync_mut/test_runner/test_runner_args.spl',
              'src/lib/nogc_sync_mut/test_runner/test_runner_types.spl',
              'src/lib/nogc_sync_mut/test_runner/test_runner_async.spl',
              'src/lib/nogc_sync_mut/test_runner/worker_memory.spl',
              'src/lib/common/convert.spl'):
            target = self.source / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(b'fixture input\n')

    def args(self, output, jobs=None, operation=None):
        args = ['phase1', '--seed', str(self.seed), '--seed-sha256',
                hashlib.sha256(self.seed.read_bytes()).hexdigest(),
                '--source-root', str(self.source), '--output-root', str(output)]
        if jobs is not None: args += ['--jobs', str(jobs)]
        if operation: args += [operation]
        return args

    def test_admitted_counts_match_child_environment_and_receipt(self):
        for jobs in (1, 20, 40, 128):
            with self.subTest(jobs=jobs):
                output = self.root / f'run-{jobs}'
                with patch('sys.argv', self.args(output, jobs)), patch.object(module.subprocess, 'run') as child:
                    child.return_value.returncode = 139
                    self.assertEqual(module.main(), 2)
                request = json.loads((output / 'request.json').read_text())
                self.assertEqual(request['jobs'], jobs)
                self.assertEqual(request['worker_memory_mb'], 0)
                self.assertFalse(any(arg.startswith('--worker-memory-mb=') for arg in child.call_args.args[0]))
                self.assertIn(f'--max-workers={jobs}', child.call_args.args[0])
                self.assertEqual(child.call_args.kwargs['env']['SIMPLE_TEST_JOBS'], str(jobs))
                self.assertEqual(request['command'], child.call_args.args[0])
                self.assertIn('--unstable', request['command'])
                self.assertIn('--whole', request['command'])
                self.assertEqual(json.loads((output / 'result.json').read_text())['status'], 'INFRASTRUCTURE_FAILED')

    def test_default_preserves_twenty(self):
        output = self.root / 'default'
        with patch('sys.argv', self.args(output, operation='--prepare-only')):
            self.assertEqual(module.main(), 0)
        self.assertEqual(json.loads((output / 'request.json').read_text())['jobs'], 20)

    def test_invalid_jobs_reject_before_launch_or_output_creation(self):
        for jobs in (0, -1, 129, 'invalid'):
            output = self.root / f'invalid-{jobs}'
            with patch('sys.argv', self.args(output, jobs)), patch.object(module.subprocess, 'run') as child, contextlib.redirect_stderr(io.StringIO()):
                with self.assertRaises(SystemExit) as error: module.main()
                self.assertEqual(error.exception.code, 2)
                child.assert_not_called()
            self.assertFalse(output.exists())

    def test_prepared_count_change_cannot_launch(self):
        output = self.root / 'prepared'
        with patch('sys.argv', self.args(output, 20, '--prepare-only')):
            self.assertEqual(module.main(), 0)
        with patch('sys.argv', self.args(output, 40, '--resume-prepared')), patch.object(module.subprocess, 'run') as child, contextlib.redirect_stderr(io.StringIO()):
            with self.assertRaises(SystemExit) as error: module.main()
            self.assertEqual(error.exception.code, 2)
            child.assert_not_called()
        self.assertFalse((output / 'stdout.log').exists())

    def test_prepared_memory_budget_change_cannot_launch(self):
        output = self.root / 'prepared-memory'
        with patch('sys.argv', self.args(output, 20, '--prepare-only')):
            self.assertEqual(module.main(), 0)
        args = self.args(output, 20, '--resume-prepared') + ['--worker-memory-mb', '10240']
        with patch('sys.argv', args), patch.object(module.subprocess, 'run') as child, contextlib.redirect_stderr(io.StringIO()):
            with self.assertRaises(SystemExit): module.main()
            child.assert_not_called()

    def test_explicit_memory_budget_reaches_child_and_receipt(self):
        output = self.root / 'explicit-memory'
        args = self.args(output, 20, '--prepare-only') + ['--worker-memory-mb', '20480']
        with patch('sys.argv', args):
            self.assertEqual(module.main(), 0)
        request = json.loads((output / 'request.json').read_text())
        self.assertEqual(request['worker_memory_mb'], 20480)
        self.assertIn('--worker-memory-mb=20480', request['command'])
        self.assertEqual(request['jobs'], 20)

    def test_invalid_memory_budget_rejects(self):
        for value in ('-1', '1048577', 'bad'):
            output = self.root / ('memory-' + value)
            args = self.args(output, 20) + ['--worker-memory-mb', value]
            with patch('sys.argv', args), patch.object(module.subprocess, 'run') as child, contextlib.redirect_stderr(io.StringIO()):
                with self.assertRaises(SystemExit): module.main()
                child.assert_not_called()
            self.assertFalse(output.exists())


if __name__ == '__main__': unittest.main()
