"""Boundary tests for real linker-input evidence; no fake compiler execution."""
import importlib.util
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
import sys
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[3]
SPEC = importlib.util.spec_from_file_location("hello_matrix", ROOT / "scripts/bootstrap/hello-sanity-matrix.py")
MATRIX = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MATRIX)


class LinkInputEvidence(unittest.TestCase):
    def test_phase2_configured_interpreter_skip_does_not_hide_native_failure(self):
        self.assertEqual(MATRIX.matrix_status(2, "PASS", "SKIPPED"), "PASS")
        self.assertEqual(MATRIX.matrix_status(2, "PARTIAL", "SKIPPED"), "PARTIAL")
        self.assertEqual(MATRIX.matrix_status(2, "FAIL", "SKIPPED"), "FAIL")
        self.assertEqual(MATRIX.matrix_status(3, "PASS", "SKIPPED"), "FAIL")
        self.assertEqual(MATRIX.matrix_status(2, "PASS", "UNRUN"), "FAIL")

    def test_task_caches_preserve_reserved_user_environment(self):
        matrix = object.__new__(MATRIX.Matrix)
        matrix.base = {"HOME": "/original/user", "home": "original-home", "CODEX_HOME": "/original/codex"}
        environment = matrix.command_environment(Path("/private/lane"))
        for key in ["HOME", "home", "CODEX_HOME"]:
            self.assertEqual(environment[key], matrix.base[key])
        self.assertEqual(environment["SIMPLE_USER_STORAGE_ROOT"], "/private/lane/storage")
        with self.assertRaises(ValueError):
            matrix.command_environment(Path("/private/lane"), {"HOME": "/repurposed"})

    def test_old_jit_argv_cannot_be_reused_as_interpreter_pass(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            prior, output, source = root / "prior", root / "out", root / "source"
            (prior / "interpreter").mkdir(parents=True)
            output.mkdir()
            (source / MATRIX.FIXTURES).mkdir(parents=True)
            (source / MATRIX.FIXTURES / "single.spl").write_bytes((ROOT / MATRIX.FIXTURES / "single.spl").read_bytes())
            compiler = Path(sys.executable)
            sha = MATRIX.digest(compiler)
            MATRIX.sdn(prior / "identity.sdn", {"single_spl_sha256": MATRIX.digest(source / MATRIX.FIXTURES / "single.spl")})
            MATRIX.sdn(prior / "runtime-inputs.sdn", {"runtime.a": "bound-runtime"})
            MATRIX.sdn(prior / "interpreter/result.sdn", {"phase": 2, "compiler_sha256": sha, "status": "PASS"})
            (prior / "interpreter/run.stdout").write_bytes(MATRIX.EXPECTED)
            (prior / "interpreter/run.stderr").write_bytes(b"")
            MATRIX.sdn(prior / "interpreter/run.sdn", {"exit_code": 0, "compiler_sha256": sha,
                "stdout_sha256": MATRIX.digest(prior / "interpreter/run.stdout"),
                "stderr_sha256": MATRIX.digest(prior / "interpreter/run.stderr")})
            (prior / "interpreter/run.argv.txt").write_text(str(compiler) + " run " + str(MATRIX.FIXTURES / "single.spl") + " --mode=interpreter --backend=llvm\n")
            matrix = object.__new__(MATRIX.Matrix)
            matrix.out, matrix.root, matrix.compiler, matrix.sha = output, source, compiler, sha
            matrix.runtime_hashes = {"runtime.a": "bound-runtime"}
            matrix.args = SimpleNamespace(phase=2, prior_interpreter_evidence=prior / "interpreter/result.sdn")
            result = matrix.interpreter()
            self.assertEqual(result["status"], "FAIL")
            self.assertIn("canonical interpreter", result["reason"])

    def test_natural_tool_metadata_never_uses_shell_evaluation(self):
        self.assertEqual(MATRIX.first_command_executable('"C:\\LLVM tools\\lld-link.exe" @args.rsp\n'),
                         'C:\\LLVM tools\\lld-link.exe')
        for malformed in ['"C:\\lld-link.exe"suffix @args', 'lld-link.exe @args\nsecond-command', '']:
            with self.assertRaises(ValueError):
                MATRIX.first_command_executable(malformed)

    def test_phase1_proxy_records_the_actual_unmodified_linker_tool(self):
        linker = shutil.which("ld.lld")
        if not linker:
            self.skipTest("real LLD transport test needs ld.lld")
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            capture = root / "link.tar"
            proxy = MATRIX.phase1_linker_proxy(root / "tool", Path(linker), capture)
            completed = subprocess.run([str(proxy), "--help"], stdout=subprocess.DEVNULL,
                                       stderr=subprocess.PIPE, timeout=5)
            self.assertEqual(completed.returncode, 0, completed.stderr)
            self.assertEqual(Path(str(capture) + ".tool.sdn").read_text(),
                             'linker_sha256: "' + MATRIX.digest(linker) + '"\n')

    def test_chroot_replay_consumes_emitted_files_outside_archive(self):
        with tempfile.TemporaryDirectory() as directory:
            outer = Path(directory)
            root = outer / "archive"
            root.mkdir()
            main, provider = outer / "main.o", outer / "provider.o"
            main.write_bytes(b"compiled main")
            provider.write_bytes(b"compiled provider")
            (root / "main.o").write_bytes(main.read_bytes())
            (root / "provider.o").write_bytes(provider.read_bytes())
            result = MATRIX.replace_inputs(["--chroot", ".", "main.o", "provider.o"], root, main, provider)
            self.assertEqual(result, ["--chroot", ".", "../main.o", "../provider.o"])
            self.assertEqual((root / result[2]).resolve(), main)

    def test_ambiguous_duplicate_link_inputs_fail_closed(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            main, provider = root / "main.o", root / "provider.o"
            main.write_bytes(b"compiled main")
            provider.write_bytes(b"compiled provider")
            with self.assertRaisesRegex(ValueError, "ambiguous"):
                MATRIX.replace_inputs(["main.o", "main.o", "provider.o"], root, main, provider)

    def test_existing_output_is_preserved_before_any_compiler_launch(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            output, runtime = root / "prior", root / "runtime"
            output.mkdir()
            runtime.mkdir()
            (runtime / "authority.a").write_bytes(b"identity fixture, never linked")
            sentinel = output / "result.sdn"
            sentinel.write_text('status: "historical"\n')
            args = SimpleNamespace(source_root=ROOT, output=output, compiler=Path(sys.executable),
                runtime_path=runtime, linker=sys.executable, lanes=list(MATRIX.LANES),
                windows_abi="msvc", max_rss_kib=1024)
            matrix = MATRIX.Matrix(args)
            with self.assertRaises(FileExistsError):
                matrix.execute()
            self.assertFalse(matrix.created_output)
            self.assertEqual(sentinel.read_text(), 'status: "historical"\n')

    def test_response_keeps_paths_with_spaces(self):
        self.assertEqual(MATRIX.response_tokens('"inputs/main space.o" -o "output space"'),
                         ["inputs/main space.o", "-o", "output space"])

    def test_nested_response_is_rejected(self):
        with self.assertRaises(ValueError):
            MATRIX.response_tokens("@unbound.rsp")

    def test_exact_input_bytes_are_required_and_replaced(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            main = root / "emitted main.o"
            provider = root / "emitted provider.o"
            main.write_bytes(b"real main object bytes")
            provider.write_bytes(b"real provider object bytes")
            (root / "captured-main.o").write_bytes(main.read_bytes())
            (root / "captured-provider.o").write_bytes(provider.read_bytes())
            actual = MATRIX.replace_inputs(["captured-main.o", "captured-provider.o", "-lc"], root, main, provider)
            self.assertEqual(actual, [str(main), str(provider), "-lc"])
            (root / "captured-main.o").write_bytes(b"different compiler bytes")
            with self.assertRaises(ValueError):
                MATRIX.replace_inputs(["captured-main.o", "captured-provider.o"], root, main, provider)

    def test_reproduction_receipt_binds_archive_output_and_linker(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            archive, output, linker = [root / name for name in ["capture.tar", "program", "ld.lld"]]
            for path in [archive, output, linker]:
                path.write_bytes(path.name.encode())
            receipt = Path(str(archive) + ".receipt")
            receipt.write_text("simple-native-link-reproduce-v1\n" + "".join(
                key + "=" + MATRIX.digest(path) + "\n" for key, path in [
                    ("archive_sha256", archive), ("output_sha256", output), ("linker_sha256", linker)]))
            MATRIX.verify_capture_receipt(archive, output, linker)
            linker.write_bytes(b"changed tool")
            with self.assertRaises(ValueError):
                MATRIX.verify_capture_receipt(archive, output, linker)


if __name__ == "__main__":
    unittest.main()
