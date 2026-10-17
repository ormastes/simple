"""Exercise production shell policy and argv builders without a compiler."""
import os
from pathlib import Path
import re
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
HELPER = ROOT / 'scripts/bootstrap/lib/stage3-source-policy.shs'
RESUME = (ROOT / 'scripts/bootstrap/resume-stage3-from-admitted.sh').read_text()
WORKER = (ROOT / 'scripts/bootstrap/lib/stage3-native-build-worker.sh').read_text()
POLICY = ['--source', '/frozen/k1', '--source', '/frozen/cuda disabled',
          '--source', 'src/compiler', '--source', 'src/app', '--source', 'src/lib',
          '--source', '/frozen/plugins dynamic', '--entry-closure']


def shell(code, args=(), env=None):
    return subprocess.run(['sh', '-c', code, 'control', *args],
                          env=env, capture_output=True, timeout=10)


def policy(mode, args):
    return shell('. "$1"; shift; bootstrap_stage3_source_policy "$@"',
                 [str(HELPER), mode, *args])


class SourcePolicy(unittest.TestCase):
    def test_exact_order_and_optional_closure(self):
        for selected in (POLICY, POLICY[:-1],
                         ['--source', 'src/plugins', '--entry-closure', '--source', 'src/lib']):
            argv = ['native-build', '--backend', 'llvm', *selected,
                    '--threads', '3', '--entry', 'src/app/cli/bootstrap_main.spl',
                    '--low-memory', '--verbose', '-o', '/output/stage2']
            result = policy('stage2', argv)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout.decode().splitlines(), selected)
            result = policy('transfer', selected)
            self.assertEqual(result.returncode, 0, result.stderr)

    def test_malformed_policy_refused(self):
        for selected in ([], ['--entry-closure'], ['--source'], ['--source', ''],
                         ['--source', '--entry-closure'], ['--source=x'],
                         ['--source', 'src\nlib'], ['--source', 'src\rlib'],
                         POLICY + ['--entry-closure'], POLICY + ['--backend', 'llvm'],
                         POLICY + ['src/app/cli/bootstrap_main.spl']):
            self.assertNotEqual(policy('transfer', selected).returncode, 0, selected)
        for argv in (['native-build'], ['native-build', '--source'],
                     ['native-build', '--unknown', 'x', *POLICY],
                     ['native-build', '--backend', '--source', 'x'],
                     ['not-native-build', *POLICY]):
            self.assertNotEqual(policy('stage2', argv).returncode, 0, argv)

    def test_authenticated_vector_reconstruction(self):
        begin = RESUME.index('. "$root/scripts/bootstrap/lib/stage3-source-policy.shs"')
        end = RESUME.index('\nEOF_STAGE3_SOURCE_POLICY', begin) + len('\nEOF_STAGE3_SOURCE_POLICY')
        code = ('root=$1; shift; bootstrap_stage3_error() { exit 64; };\n' +
                RESUME[begin:end] + '\nprintf "%s\\0" "$@"')
        result = shell(code, [str(ROOT), 'native-build', '--backend', 'llvm', *POLICY])
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.split(b'\0')[:-1], [p.encode() for p in POLICY])
        self.assertNotEqual(shell(code, [str(ROOT), 'native-build']).returncode, 0)
        self.assertLess(RESUME.index('bootstrap_stage3_verify_stage2_admission_receipt'), begin)

    def test_real_digest_and_worker_builders_match(self):
        begin = RESUME.index('stage3_args=$(bootstrap_stage3_args_sha256')
        end = RESUME.index('src/app/cli/bootstrap_main.spl)', begin) + len('src/app/cli/bootstrap_main.spl)')
        digest = RESUME[begin:end]
        launch = WORKER[WORKER.index('bootstrap_stage3_run_transcribed "$transcript"'):]
        with tempfile.TemporaryDirectory() as temporary:
            record = Path(temporary) / 'argv'
            for selected in (POLICY, POLICY[:-1]):
                vectors = []
                for function, code in [('bootstrap_stage3_args_sha256', digest),
                                       ('bootstrap_stage3_run_transcribed', launch)]:
                    env = os.environ.copy()
                    for name in re.findall(r'\$(?:\{)?([A-Za-z_][A-Za-z_0-9]*)', code):
                        env[name] = 'fixture'
                    for name in ('stage3_timeout_args', 'timeout_args', 'stage3_mc_env',
                                 'mc_env', 'stage3_cold_init_env', 'cold_env',
                                 'stage3_diagnostic_env', 'diagnostic_env'):
                        env[name] = ''
                    env['CONTROL_RECORD'] = str(record)
                    stub = function + '() { printf "%s\\0" "$@" >"$CONTROL_RECORD"; };\n'
                    result = shell(stub + code, selected, env)
                    self.assertEqual(result.returncode, 0, result.stderr)
                    args = record.read_bytes().split(b'\0')[:-1]
                    vectors.append(args[args.index(b'native-build'):])
                self.assertEqual(vectors[0], vectors[1])
                self.assertEqual(vectors[0][-len(selected)-1:-1], [p.encode() for p in selected])

    def test_all_four_launches_transfer_typed_prefix_and_policy(self):
        branches = re.findall(r'"\$worker" "\$stage3_transcript".*? &', RESUME, re.S)
        self.assertEqual(len(branches), 4)
        for branch in branches:
            env = os.environ.copy()
            for name in re.findall(r'\$([A-Za-z_][A-Za-z_0-9]*)', branch):
                env[name] = name
            env['worker'] = 'record'
            result = shell('record() { printf "%s\\0" "$@"; };\n' + branch[:-2], POLICY, env)
            self.assertEqual(result.returncode, 0, result.stderr)
            args = result.stdout.split(b'\0')[:-1]
            self.assertEqual(args[28], b'stage3_rss_cap_mode')
            self.assertEqual(args[29:], [p.encode() for p in POLICY])

    def test_worker_prefix_rejects_missing_policy_and_invalid_rss(self):
        prefix = WORKER[:WORKER.index('BOOTSTRAP_STAGE3_FACADE_PATH=')]
        for mode in ('enforce', 'monitor', 'invalid'):
            args = ['fixture'] * 29
            args[1] = str(ROOT)
            args[28] = mode
            result = shell(prefix + '\nprintf "%s\\0" "$@"', args + POLICY)
            self.assertEqual(result.returncode, 0 if mode != 'invalid' else 64, result.stderr)
            if mode != 'invalid':
                self.assertEqual(result.stdout.split(b'\0')[:-1], [p.encode() for p in POLICY])
        self.assertEqual(shell(prefix, args).returncode, 64)
        self.assertEqual(shell(prefix, args + ['--source', '']).returncode, 64)


if __name__ == '__main__':
    unittest.main()
