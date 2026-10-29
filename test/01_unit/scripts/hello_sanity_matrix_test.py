"""Boundary tests for real linker-input evidence; no fake compiler execution."""
import importlib.util
import json
import os
from unittest import mock
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

DARWIN_SPEC = importlib.util.spec_from_file_location("hello_matrix_darwin", ROOT / "scripts/bootstrap/hello-sanity-matrix-darwin.py")
DARWIN = importlib.util.module_from_spec(DARWIN_SPEC)
DARWIN_SPEC.loader.exec_module(DARWIN)


class LinkInputEvidence(unittest.TestCase):
    def test_phase_capabilities_and_seed_interpreter_selection(self):
        self.assertEqual(MATRIX.phase_capabilities(1), (True, False))
        self.assertEqual(MATRIX.phase_capabilities(2), (False, True))
        self.assertEqual(MATRIX.phase_capabilities(3), (True, True))
        argv, env = MATRIX.interpreter_invocation(1, Path("/phase1"))
        self.assertEqual(argv, [Path("/phase1"), "run", str(MATRIX.FIXTURES / "single.spl")])
        self.assertEqual(env["SIMPLE_EXECUTION_MODE"], "interpret")
        self.assertIn("--interpret", MATRIX.interpreter_invocation(3, Path("/phase3"))[0])

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
            self.assertEqual((root / result[2]).resolve(), main.resolve())

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

    def test_darwin_capture_preserves_hosted_inputs_and_rejects_tampering(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            driver, linker, main, provider, shim, program = [root / name for name in
                ["clang", "ld64.lld", "main.o", "provider.o", "hosted-entry.o", "program"]]
            for path in [driver, linker, main, provider, shim, program]:
                path.write_bytes(path.name.encode())
            capture = root / "link.json"
            record = {"driver": str(driver), "driver_sha256": MATRIX.digest(driver),
                      "linker": str(linker), "linker_sha256": MATRIX.digest(linker),
                      "cwd": str(root), "output": str(program), "output_sha256": MATRIX.digest(program),
                      "inputs": {str(p): MATRIX.digest(p) for p in [main, provider, shim]},
                      "argv": ["--ld-path=" + str(linker), "--no-default-config", str(main), str(provider), str(shim), "-o", str(program)]}
            capture.write_text(json.dumps(record))
            command, cwd = DARWIN.replay_inputs(capture, program, driver, linker, main, provider, root / "hello")
            self.assertIn(str(shim), command)
            self.assertEqual(command[-2:], ["-o", str(root / "hello")])
            self.assertEqual(cwd, root)
            shim.write_bytes(b"unbound replacement")
            with self.assertRaisesRegex(ValueError, "input changed"):
                DARWIN.replay_inputs(capture, program, driver, linker, main, provider, root / "hello")

    def test_darwin_rejects_opaque_and_driver_override_arguments(self):
        for arg in ["-Wl,@hidden.rsp", "-Wl,-filelist,hidden.list", "--config=hidden.cfg"]:
            with self.subTest(arg=arg), self.assertRaisesRegex(ValueError, "opaque"):
                DARWIN.capture_link("unavailable-driver", "unavailable-linker", "unused", [arg])

    @unittest.skipUnless(sys.platform == "darwin" and shutil.which("ld64.lld"), "requires real Darwin Mach-O tools")
    def test_darwin_real_driver_capture_and_all_four_linkage_forms(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            driver, linker = DARWIN.resolve_driver(), Path(shutil.which("ld64.lld"))
            sdk = DARWIN.resolve_sdk()
            def run(argv):
                return subprocess.run(list(map(str, argv)), check=True, capture_output=True, timeout=15, env=os.environ | {"SDKROOT": str(sdk)})
            main_c, provider_c = root / "main.c", root / "provider.c"
            main_c.write_text('#include <stdio.h>\nextern int hello_value(void);\nint main(void) { if (hello_value() != 42) return 1; puts("Hello, World!"); return 0; }\n')
            provider_c.write_text('int hello_value(void) { return 42; }\n')
            single = root / "single.c"
            single.write_text(provider_c.read_text() + main_c.read_text())
            run([driver, "--ld-path=" + str(linker), single, "-o", root / "single"])
            self.assertEqual(run([root / "single"]).stdout, MATRIX.EXPECTED)
            main, provider = root / "main.o", root / "provider.o"
            run([driver, "-c", main_c, "-o", main])
            run([driver, "-c", provider_c, "-o", provider])
            archive, shared = root / "libhello.a", root / "libhello.dylib"
            run(["ar", "rcs", archive, provider])
            run([driver, "--ld-path=" + str(linker), "-dynamiclib", provider,
                 "-Wl,-install_name,@loader_path/libhello.dylib", "-o", shared])
            for form, linked in [("object", provider), ("archive", archive), ("shared", shared)]:
                capture = root / (form + ".json")
                proxy = DARWIN.capture_proxy(root / (form + "-tool"), driver, linker, capture)
                natural, output = root / (form + "-natural"), root / form
                with mock.patch.dict(os.environ, {"CCC_OVERRIDE_OPTIONS": "+--ld-path=/nonexistent/unbound-linker"}):
                    run([proxy, main, linked, "-o", natural])
                command, cwd = DARWIN.replay_inputs(capture, natural, driver, linker, main, linked, output)
                run(command)
                completed = run([output])
                self.assertEqual(completed.stdout, MATRIX.EXPECTED)
                self.assertEqual(completed.stderr, b"")
                if form == "shared":
                    self.assertIn(b"@loader_path/libhello.dylib", run(["otool", "-L", output]).stdout)
                    self.assertIn(b"_hello_value", run(["nm", "-gU", shared]).stdout)

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
