"""Exercise production evidence gates with fixtures, never claim native execution.

The image header and runner transcript below are deliberately synthetic. They
test validation and invocation contracts only; live qualification needs the
admitted pure-Simple producer and real compiled SSpec artifacts.
"""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[3]
VALIDATOR = ROOT / "scripts/bootstrap/validate-native-aot-evidence.pl"
WRAPPER = ROOT / "scripts/bootstrap/run-native-aot-suite.shs"


class NativeEvidenceContract(unittest.TestCase):
    def fixture(self, root, backend="llvm"):
        source = root / "source"
        suite = "test/example_spec.spl"
        (source / "test").mkdir(parents=True)
        (source / suite).write_text("# Evidence parser fixture, not an executed spec\n")
        compiler = root / "compiler"
        compiler.write_bytes(b"pinned producer fixture")
        sha = hashlib.sha256(compiler.read_bytes()).hexdigest()
        private = root / "tmp"
        private.mkdir()
        artifact = private / (backend + "-" + sha[:16])
        artifact.write_bytes(b"\x7fELFsynthetic evidence-parser fixture")
        artifact.chmod(0o700)
        argv = ["native-build", "--backend", backend, "--refresh-source-authority",
                "--entry-closure", "--entry", str(private / "entry.spl"),
                "--runtime-bundle", "core-c-bootstrap", "--threads", "2",
                "--cache-dir", str(artifact) + ".cache", "--output", str(artifact)]
        invocation = {"backend": backend, "producer_sha256": sha,
                      "spec": suite, "output": str(artifact),
                      "compiler": str(compiler), "argv": argv}
        passed = "  PASS  " + suite + " (3 passed, 12ms)"
        lines = ["native-aot-invocation|" + json.dumps(invocation),
                 "[native] Running " + str(artifact), passed,
                 "Results: 3 total, 3 passed, 0 failed"]
        log, receipt = root / "runner.log", root / "evidence.tsv"
        args = ["perl", str(VALIDATOR), str(log), str(private), str(source),
                suite, backend, str(compiler), sha, "2", "", "a" * 64, str(receipt)]
        return {"source": source, "suite": suite, "compiler": compiler,
                "private": private, "artifact": artifact, "invocation": invocation,
                "lines": lines, "log": log, "receipt": receipt, "args": args}

    def validate(self, f):
        f["log"].write_text("\n".join(f["lines"]) + "\n")
        return subprocess.run(f["args"], capture_output=True, text=True, timeout=5)

    def test_supported_text_accepts_both_backends_and_retains_bound_sample(self):
        for backend in ("llvm", "cranelift"):
            with self.subTest(backend=backend), tempfile.TemporaryDirectory() as temp:
                f = self.fixture(Path(temp).resolve(), backend)
                expected = hashlib.sha256(f["artifact"].read_bytes()).hexdigest()
                # Current text output permits an optional setup duration.
                f["lines"][2] += " [setup: 4ms]"
                result = self.validate(f)
                self.assertEqual(result.returncode, 0, result.stderr)
                receipt = f["receipt"].read_text()
                self.assertIn("assertions_passed=3\n", receipt)
                self.assertIn("backend=" + backend + "\n", receipt)
                self.assertIn(expected, receipt)
                self.assertEqual(hashlib.sha256((Path(temp) / "sample-artifact").read_bytes()).hexdigest(), expected)
                self.assertFalse(f["private"].exists())

    def test_invalid_text_evidence_never_publishes_receipt_or_deletes_artifacts(self):
        mutations = {
            "missing-file-result": lambda x: x.pop(2),
            "duplicate-file-result": lambda x: x.insert(2, x[2]),
            "zero-executed": lambda x: x.__setitem__(2, x[2].replace("3 passed", "0 passed")),
            "cached": lambda x: x.__setitem__(2, x[2] + " [cached]"),
            "skipped": lambda x: x.__setitem__(2, x[2].replace("3 passed", "3 passed, 1 skipped")),
            "pending": lambda x: x.__setitem__(2, x[2].replace("3 passed", "3 passed, 1 pending")),
            "failed": lambda x: x.__setitem__(2, x[2].replace("PASS", "FAIL")),
            "timeout": lambda x: x.__setitem__(2, "  TOUT  test/example_spec.spl (12ms)"),
            "error": lambda x: x.insert(3, "        Error: owner failed"),
            "unexpected-file": lambda x: x.__setitem__(2, x[2].replace("example_spec", "extra_spec")),
            "missing-total": lambda x: x.pop(3),
            "duplicate-total": lambda x: x.append(x[3]),
            "inconsistent-total": lambda x: x.__setitem__(3, "Results: 2 total, 2 passed, 0 failed"),
            "failed-total": lambda x: x.__setitem__(3, "Results: 4 total, 3 passed, 1 failed"),
            "skipped-total": lambda x: x.__setitem__(3, x[3] + ", 1 skipped"),
            "pending-total": lambda x: x.__setitem__(3, x[3] + ", 1 pending"),
            "cached-total": lambda x: x.__setitem__(3, x[3] + ", 1 cached"),
            "missing-execution": lambda x: x.pop(1),
            "duplicate-execution": lambda x: x.insert(1, x[1]),
            "missing-invocation": lambda x: x.pop(0),
            "duplicate-invocation": lambda x: x.insert(0, x[0]),
            "fallback": lambda x: x.append("interpreter-fallback"),
            "legacy-json": lambda x: x.append('{"success":true,"spec":{"success":true}}'),
        }
        for name, mutate in mutations.items():
            with self.subTest(case=name), tempfile.TemporaryDirectory() as temp:
                f = self.fixture(Path(temp).resolve())
                mutate(f["lines"])
                result = self.validate(f)
                self.assertNotEqual(result.returncode, 0, name)
                self.assertFalse(f["receipt"].exists(), name)
                self.assertTrue(f["artifact"].exists(), name)

    def test_wrong_native_identity_and_artifacts_are_rejected(self):
        for field, replacement in (("backend", "cranelift"), ("producer_sha256", "b" * 64),
                                   ("compiler", "/different/compiler"), ("spec", "test/wrong_spec.spl")):
            with self.subTest(field=field), tempfile.TemporaryDirectory() as temp:
                f = self.fixture(Path(temp).resolve())
                f["invocation"][field] = replacement
                f["lines"][0] = "native-aot-invocation|" + json.dumps(f["invocation"])
                result = self.validate(f)
                self.assertNotEqual(result.returncode, 0)
                self.assertFalse(f["receipt"].exists())
        for kind in ("missing", "nonexecutable", "text", "changed-producer", "linked"):
            with self.subTest(artifact=kind), tempfile.TemporaryDirectory() as temp:
                f = self.fixture(Path(temp).resolve())
                if kind == "missing":
                    f["artifact"].unlink()
                elif kind == "nonexecutable":
                    f["artifact"].chmod(0o600)
                elif kind == "text":
                    f["artifact"].write_bytes(b"#!/bin/sh\nexit 0\n")
                elif kind == "changed-producer":
                    f["compiler"].write_bytes(b"changed")
                else:
                    target = Path(temp) / "external-image"
                    f["artifact"].rename(target)
                    f["artifact"].symlink_to(target)
                result = self.validate(f)
                self.assertNotEqual(result.returncode, 0)
                self.assertFalse(f["receipt"].exists())

    def test_wrong_argv_and_omitted_suite_file_are_rejected(self):
        for option in ("--backend", "--threads", "--output", "--cache-dir", "--runtime-bundle"):
            with self.subTest(option=option), tempfile.TemporaryDirectory() as temp:
                f = self.fixture(Path(temp).resolve())
                argv = f["invocation"]["argv"]
                argv[argv.index(option) + 1] = "wrong"
                f["lines"][0] = "native-aot-invocation|" + json.dumps(f["invocation"])
                self.assertNotEqual(self.validate(f).returncode, 0)
                self.assertFalse(f["receipt"].exists())
        with tempfile.TemporaryDirectory() as temp:
            f = self.fixture(Path(temp).resolve())
            (f["source"] / "test/omitted_spec.spl").write_text("# not executed\n")
            f["args"][5] = "test"
            self.assertNotEqual(self.validate(f).returncode, 0)
            self.assertFalse(f["receipt"].exists())

    def test_wrapper_selects_supported_text_and_preserves_runner_failure(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp).resolve()
            runner = root / "runner"
            runner.write_text("#!" + sys.executable + "\n" +
                "import os, sys\nfrom pathlib import Path\n" +
                "Path(os.environ['TMPDIR']).joinpath('argv').write_text('\\n'.join(sys.argv[1:]))\n" +
                "print('fixture runner failure')\nsys.exit(19)\n")
            runner.chmod(0o700)
            run = root / "run"
            run.mkdir()
            result = subprocess.run(["sh", str(WRAPPER), str(ROOT), "llvm", str(runner),
                hashlib.sha256(runner.read_bytes()).hexdigest(), str(runner), "test/example_spec.spl",
                str(run), "2", "-", "a" * 64], capture_output=True, text=True, timeout=5)
            self.assertEqual(result.returncode, 19, result.stderr)
            argv = (run / "tmp/argv").read_text().splitlines()
            self.assertNotIn("--json", argv)
            self.assertEqual(argv[argv.index("--format") + 1], "text")
            for option in ("--assert-ran", "--no-cache", "--no-session-daemon", "--sequential", "--keep-artifacts"):
                self.assertIn(option, argv)
            self.assertFalse((run / "evidence.tsv").exists())
            self.assertIn("fixture runner failure", (run / "runner.log").read_text())


if __name__ == "__main__":
    unittest.main()
