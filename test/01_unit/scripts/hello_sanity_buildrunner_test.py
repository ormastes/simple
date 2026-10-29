import importlib.util
from pathlib import Path
import tempfile
import types
import unittest

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
                args=types.SimpleNamespace(phase=2, max_rss_kib=1024, timeout_seconds=10))
            matrix.run = lambda lane, name, argv: (b"builder: verified tasks=1\n", b"")
            result = module.run_one_source(matrix, "llvm", root / "manager", root / "writer", root / "template", "x86_64-linux")
            self.assertEqual(result["status"], "FAIL")
            self.assertIn("receipt", result["reason"])


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
            memory.write_text(memory.read_text() + "enforcement=job-memory\n")
            with self.assertRaisesRegex(ValueError, "duplicate"):
                module.verified_memory_receipt(root, receipt, "hello", artifact, 1024)


if __name__ == "__main__":
    unittest.main()
