import importlib.util
from pathlib import Path
import tempfile
import types
import unittest
from unittest import mock
import hashlib
import os
import zipfile

ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location("hello_buildrunner", ROOT / "scripts/bootstrap/hello-sanity-buildrunner.py")
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class MissingReceiptTest(unittest.TestCase):
    def test_manager_exit_alone_does_not_pass_without_receipt(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            runtime = root / "runtime"
            runtime.mkdir()
            (runtime / "lib.a").write_bytes(b"runtime")
            for name in ("manager", "writer", "template"):
                (root / name).write_bytes(b"fixture")
            matrix = types.SimpleNamespace(out=root, root=ROOT, runtime=runtime,
                compiler=root / "simple", sha="a" * 64,
                linker=Path("/usr/bin/ld"), runtime_hashes={"lib.a": module.matrix_digest(runtime / "lib.a")},
                args=types.SimpleNamespace(phase=2, max_rss_kib=1024, timeout_seconds=10,
                    compile_route="positional", min_free_disk_bytes=0, max_log_bytes=1024,
                    windows_abi="msvc"))
            matrix.compiler.write_bytes(b"compiler")
            matrix.sha = module.matrix_digest(matrix.compiler)
            commands = []
            def run(lane, name, argv, **kwargs):
                if name == "manifest":
                    commands.append(argv)
                return b"builder: verified tasks=1\n", b""
            matrix.run = run
            with mock.patch("platform.machine", return_value="x86_64"), mock.patch("sys.platform", "linux"):
                for backend in ("llvm", "cranelift"):
                    for lane in ("one-source", "two-objects", "static-library", "shared-library"):
                        result = module.run_lane(matrix, backend, lane, root / "manager", root / "writer", root / "template", "x86_64-linux")
                        self.assertEqual(result["status"], "FAIL")
                        self.assertIn("receipt", result["reason"])
                        command = commands[-1]
                        self.assertEqual(command[command.index("--lane") + 1], lane)
                        self.assertEqual(command[command.index("--backend") + 1], backend)
                        self.assertEqual(command[command.index("--target") + 1], "x86_64-linux")
            self.assertEqual(len(commands), 8)


    def test_memory_receipt_binds_result_and_rejects_duplicates(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            artifact = root / "hello"
            artifact.write_bytes(b"hello")
            identity = "a" * 64
            receipt = root / "receipt"
            receipt.write_text("\n".join(["SIMPLE-BUILD-RESULT-1", "hello", "2", identity,
                "worker1", "OK", "0", "0", "0", "0", "1", "hello", module.matrix_digest(artifact)]) + "\n")
            memory = root / "attempts/hello/2/worker1/compiler.memory"
            memory.parent.mkdir(parents=True)
            memory.write_text("format=simple-build-memory-v1\ntask_identity=" + identity +
                "\nrequested_policy=enforce\nreserved_bytes=1024\nenforcement=job-memory\n"
                "enforced_bytes=1024\nobserved_peak_bytes=500\npeak_metric=job-commit-peak\n")
            self.assertEqual(module.verified_memory_receipt(root, receipt, "hello", artifact, 1024), memory)
            enforced = memory.read_text()
            memory.write_text(enforced.replace("enforcement=job-memory", "enforcement=rss-watchdog"))
            with self.assertRaisesRegex(ValueError, "memory enforcement"):
                module.verified_memory_receipt(root, receipt, "hello", artifact, 1024)
            memory.write_text(enforced)
            memory.write_text(memory.read_text() + "enforcement=job-memory\n")
            with self.assertRaisesRegex(ValueError, "duplicate"):
                module.verified_memory_receipt(root, receipt, "hello", artifact, 1024)

    def test_cross_abi_target_rejected_before_staging(self):
        for target in ("x86_64-unknown-notlinux", "x86_64-linux-musl"):
            with self.subTest(target=target), tempfile.TemporaryDirectory() as temp:
                root = Path(temp)
                matrix = types.SimpleNamespace(out=root, sha="a" * 64,
                    args=types.SimpleNamespace(phase=2, compile_route="positional", windows_abi="msvc"))
                with mock.patch("platform.machine", return_value="x86_64"), mock.patch("sys.platform", "linux"):
                    result = module.run_lane(matrix, "llvm", "one-source", "missing", "missing", "missing", target)
                self.assertEqual(result["status"], "FAIL")
                self.assertIn("target differs", result["reason"])
                self.assertFalse((root / "buildrunner-llvm-one-source/source").exists())


class BundleTest(unittest.TestCase):
    def bundle(self, root, lane="one-source", backend="llvm", extra=None):
        expected = {"format": "hello-buildrunner-lane-v1", "lane": lane,
            "backend": backend, "phase": 2, "compile_route": "positional",
            "compiler_sha256": "a" * 64, "status": "PASS", "admitted": "false"}
        import json
        identity = "".join(f"{key}: {value if key == 'admitted' else json.dumps(value)}\n"
                           for key, value in expected.items())
        result = "".join(f"{key}: {json.dumps(expected[key])}\n" for key in
                         ("phase", "compiler_sha256", "compile_route", "status"))
        result += f'executable_sha256: "{hashlib.sha256(b"artifact").hexdigest()}"\n'
        path = root / "bundle.zip"
        with zipfile.ZipFile(path, "w") as archive:
            archive.writestr("managed-lane.sdn", identity)
            archive.writestr("result.sdn", result)
            archive.writestr("hello.exe" if os.name == "nt" else "hello", b"artifact")
            if extra:
                archive.writestr(*extra)
        return path, expected

    def test_all_four_forms_and_both_backends_require_exact_identity(self):
        for lane in ("one-source", "two-objects", "static-library", "shared-library"):
            for backend in ("llvm", "cranelift"):
                with self.subTest(lane=lane, backend=backend), tempfile.TemporaryDirectory() as temp:
                    root = Path(temp)
                    bundle, expected = self.bundle(root, lane, backend)
                    artifact = module.unpack_verified_lane(bundle, root / "verified", expected)
                    self.assertEqual(artifact.read_bytes(), b"artifact")
                    expected["backend"] = "cranelift" if backend == "llvm" else "llvm"
                    with self.assertRaisesRegex(ValueError, "identity mismatch"):
                        module.unpack_verified_lane(bundle, root / "invalid", expected)

    def test_rejects_path_traversal_before_extracting(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            bundle, expected = self.bundle(root, extra=("../escaped", b"bad"))
            with self.assertRaisesRegex(ValueError, "unsafe"):
                module.unpack_verified_lane(bundle, root / "verified", expected)
            self.assertFalse((root / "escaped").exists())

    def test_rejects_duplicate_members(self):
        import warnings
        with tempfile.TemporaryDirectory() as temp, warnings.catch_warnings():
            warnings.simplefilter("ignore", UserWarning)
            root = Path(temp)
            bundle, expected = self.bundle(root, extra=("result.sdn", b"status: \"PASS\"\n"))
            with self.assertRaisesRegex(ValueError, "ambiguous"):
                module.unpack_verified_lane(bundle, root / "verified", expected)

    def test_rejects_artifact_changed_after_worker_result(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            bundle, expected = self.bundle(root)
            corrupted = root / "corrupted.zip"
            with zipfile.ZipFile(bundle) as source, zipfile.ZipFile(corrupted, "w") as destination:
                for name in source.namelist():
                    destination.writestr(name, b"modified" if name in {"hello", "hello.exe"} else source.read(name))
            with self.assertRaisesRegex(ValueError, "executable identity"):
                module.unpack_verified_lane(corrupted, root / "verified", expected)


if __name__ == "__main__":
    unittest.main()
