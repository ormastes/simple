#!/usr/bin/env python3
"""Exercise production row dispatch without executing a compiler or runner."""
import subprocess
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).parents[1] / "bootstrap-phase-verification.shs"
SOURCE = SCRIPT.read_text()
FUNCTION = "run_repository_test_row() {" + SOURCE.split(
    "run_repository_test_row() {", 1
)[1].split("\nrun_repository_full_tests() {", 1)[0]


class RepositoryNativeRow(unittest.TestCase):
    def dispatch(self, directory, execution, backend="llvm", status=0):
        # Replace only the process/measurement boundary, not production dispatch.
        shell = FUNCTION + '''
run_measured_timeout() { printf '%s\\n' "$@"; return "$expected_status"; }
row_dir=$1
repository_test_execution=$2
verification_backend=$3
expected_status=$4
row_rss_file="$row_dir/1.max-rss-kib"
spec_timeout_seconds=120
test_runner=/authority/simple_test_runner
relative=test/01_unit/compiler/sample_spec.spl
source_root=/frozen/source
compiler_cli=/authority/simple_cli
compiler_cli_sha=aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
runtime_path=/authority/runtime
runtime_cache_identity=bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb
build_threads=2
spec_count=1
run_repository_test_row
'''
        return subprocess.run(
            ["sh", "-c", shell, "row-test", str(directory), execution, backend, str(status)],
            capture_output=True, text=True, check=False,
        )

    def test_interpreter_keeps_existing_measured_argv_and_no_native_directory(self):
        with tempfile.TemporaryDirectory() as directory:
            result = self.dispatch(directory, "interpreter")
            self.assertEqual(result.returncode, 0)
            self.assertEqual(result.stdout.splitlines(), [
                directory + "/1.max-rss-kib", "120", "15", "/authority/simple_test_runner",
                "test/01_unit/compiler/sample_spec.spl", "--mode=interpreter", "--unstable",
                "--assert-ran", "--no-cache", "--no-db", "--no-session-daemon", "--sequential", "--json",
            ])
            self.assertEqual(list(Path(directory).iterdir()), [])

    def test_each_backend_uses_existing_validator_helper_and_fresh_private_tuple(self):
        with tempfile.TemporaryDirectory(prefix="native row ") as directory:
            private_dirs = []
            for backend in ("llvm", "cranelift"):
                result = self.dispatch(directory, "native", backend)
                self.assertEqual(result.returncode, 0, result.stderr)
                argv = result.stdout.splitlines()
                private_dirs.append(argv[11])
                self.assertEqual(argv[:11], [
                    directory + "/1.max-rss-kib", "120", "15", "sh",
                    "/frozen/source/scripts/bootstrap/run-native-aot-suite.shs", "/frozen/source",
                    backend, "/authority/simple_cli", "a" * 64, "/authority/simple_test_runner",
                    "test/01_unit/compiler/sample_spec.spl",
                ])
                self.assertEqual(argv[12:], ["2", "/authority/runtime", "b" * 64])
                self.assertTrue(Path(private_dirs[-1]).is_dir())
                self.assertNotIn("--whole", argv)
            self.assertNotEqual(*private_dirs)

    def test_helper_failure_and_timeout_propagate_without_deleting_private_evidence(self):
        with tempfile.TemporaryDirectory() as directory:
            for status in (1, 124):
                result = self.dispatch(directory, "native", status=status)
                self.assertEqual(result.returncode, status)
                self.assertTrue(Path(result.stdout.splitlines()[11]).is_dir())

    def test_native_option_rejects_non_stage3_before_compiler_execution(self):
        result = subprocess.run(
            ["sh", str(SCRIPT), "--phase=stage2", "--test-execution=native"],
            capture_output=True, text=True, check=False,
        )
        self.assertEqual(result.returncode, 2)
        self.assertIn("--test-execution=native is stage3-only", result.stderr)


if __name__ == "__main__":
    unittest.main()
