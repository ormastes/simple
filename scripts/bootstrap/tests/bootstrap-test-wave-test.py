"""Control-flow tests; these fixtures confer no native/test-suite admission."""
import hashlib
import importlib.util
import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

SCRIPTS = Path(__file__).resolve().parents[1]


def load(name):
    spec = importlib.util.spec_from_file_location(name.replace('-', '_'), SCRIPTS / (name + '.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


GATE = load('phase1-terminal-gate')
WAVE = load('run-bootstrap-test-wave')
PHASE1 = load('phase1-whole-tests')


class WaveTests(unittest.TestCase):
    def test_terminal_failure_unblocks_but_never_becomes_pass(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'request.json').write_text('{}')
            request = GATE.digest(root / 'request.json')
            WAVE.ensure_phase1_terminal(root, 125, request)
            result = GATE.validate_terminal(root / 'result.json', request)
            self.assertEqual(result['status'], 'INFRASTRUCTURE_FAILED')
            self.assertEqual(result['process_exit'], 125)
            self.assertIsNone(result['runner_summary'])
            with self.assertRaises(ValueError):
                GATE.validate_terminal(root / 'result.json', 'a' * 64)
            (root / 'stdout.log').write_text('tampered')
            with self.assertRaises(ValueError):
                GATE.validate_terminal(root / 'result.json', request)

    def test_prepared_phase1_runs_no_child_and_rejects_modified_request(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / 'source'
            for name in ('config/simple.test.sdn', 'config/sdoctest.sdn',
                         'src/app/test_runner_new/main.spl',
                         'src/app/test_runner_new/test_runner_main.spl',
                         'src/lib/nogc_sync_mut/test_runner/test_runner_files.spl'):
                path = source / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text('test fixture; not native source')
            seed = root / 'seed'
            seed.write_bytes(b'fixture-only')
            output = root / 'output'
            argv = ['phase1', '--source-root', str(source), '--output-root', str(output),
                    '--seed', str(seed), '--seed-sha256', GATE.digest(seed), '--jobs', '20']
            with patch('sys.argv', argv + ['--prepare-only']), patch.object(PHASE1.subprocess, 'run') as child:
                self.assertEqual(PHASE1.main(), 0)
                child.assert_not_called()
            self.assertFalse((output / 'result.json').exists())
            request = json.loads((output / 'request.json').read_text())
            request['jobs'] = 10
            (output / 'request.json').write_text(json.dumps(request))
            with patch('sys.argv', argv + ['--resume-prepared']), patch.object(PHASE1.subprocess, 'run') as child:
                with self.assertRaises(SystemExit):
                    PHASE1.main()
                child.assert_not_called()

    def test_all_preparation_precedes_barrier_and_failures_do_not_cancel_peers(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            script = r'''
set -eu
. "$SCHEDULE"
statuses=journal
: > "$statuses"
product_phase=phase2
product_defer_full=1
product_prerequisite_ready() { return 0; }
build_test_product() {
  printf 'build:%s:%s\n' "$1" "$2" >> events
  [ "$1:$2" != llvm:loader ]
}
enumerate_test_product() { printf 'smoke:%s:%s\n' "$1" "$2" >> events; }
product_wait_phase1_terminal() { printf 'barrier:FAIL\n' >> events; }
run_test_product() {
  printf 'full:%s:%s\n' "$1" "$2" >> events
  [ "$1:$2" != llvm:compiler ]
}
result=0
managed_dispatch_products || result=$?
[ "$result" = 1 ]
'''
            env = os.environ.copy()
            env['SCHEDULE'] = (SCRIPTS / 'lib/managed-task-schedule.shs').as_posix()
            result = subprocess.run(['sh', '-c', script], cwd=root, env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            events = (root / 'events').read_text().splitlines()
            barrier = events.index('barrier:FAIL')
            self.assertEqual(sum(line.startswith('build:') for line in events[:barrier]), 6)
            self.assertEqual(sum(line.startswith('smoke:') for line in events[:barrier]), 5)
            self.assertFalse(any(line.startswith('full:') for line in events[:barrier]))
            self.assertEqual(len(events[barrier + 1:]), 5)
            self.assertEqual(events[-1], 'full:cranelift:loader')
            journal = (root / 'journal').read_text()
            self.assertIn('phase2_llvm_product_loader_run\tBLOCKED\t1', journal)
            self.assertIn('phase2_llvm_product_compiler_run\tFAILED\t1', journal)


if __name__ == '__main__':
    unittest.main()
