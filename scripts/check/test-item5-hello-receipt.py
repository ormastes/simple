#!/usr/bin/env python3
"""Receipt protocol tests with fake commands; not Simple qualification."""
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import struct
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location("receipt", HERE / "lib/item5-hello-receipt.py")
receipt = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(receipt)


class ReceiptTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="hello-receipt-test-")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.source = self.root / "source"
        self.source.mkdir()
        self.fixture = self.source / "test/04_smoke/bootstrap_hello_world.spl"
        self.fixture.parent.mkdir(parents=True)
        self.fixture.write_text('fn main() -> i64:\n    print "hello"\n    0\n')
        self.git("init", "-q")
        self.git("add", ".")
        self.git("-c", "user.name=fixture", "-c", "user.email=fixture@example.invalid",
                 "-c", "commit.gpgsign=false", "commit", "-qm", "fixture")
        self.candidate = self.root / "candidate"
        self.candidate.write_text('#!/bin/sh\nset -eu\nout=""; prev=""\n'
                                  'for arg in "$@"; do\n'
                                  '  if [ "$prev" = --output ]; then out=$arg; fi\n'
                                  '  prev=$arg\ndone\n'
                                  'printf \'#!/bin/sh\\nprintf "hello\\\\n"\\n\' > "$out"\n'
                                  'chmod +x "$out"\n')
        self.candidate.chmod(0o755)
        self.runtime = self.root / "libsimple_native_all.a"
        self.runtime.write_bytes(b"test-only runtime identity; no native linking")
        self.identity = {
            "schema": "item5-phase2-producer-identity-v1",
            "compiler_sha256": receipt.digest(self.candidate),
            "source_commit": self.git("rev-parse", "HEAD"),
            "source_tree_oid": self.git("rev-parse", "HEAD^{tree}"),
            "runtime_archive_sha256": receipt.digest(self.runtime),
            "backend": "llvm", "target": "x86_64-unknown-linux-gnu",
            "producer_backend": "cranelift",
        }
        self.identity_path = self.root / "identity.json"
        self.identity_path.write_text(json.dumps(self.identity))
        self.output = self.root / "hello.json"
        self.work = self.root / "work"
        self.work.mkdir()

    def git(self, *args):
        return subprocess.check_output(["git", "-C", str(self.source), *args], stderr=subprocess.PIPE).decode().strip()

    def capture(self):
        return receipt.capture(self.candidate, self.identity_path, self.source, self.runtime,
                               "llvm", self.identity["target"], self.fixture, self.output,
                               HERE / "check-stage2-hello-world-native-build.shs")

    def artifacts(self):
        snapshot = self.capture()
        (self.work / "receipt-inputs.json").write_text(json.dumps(snapshot))
        for name, value in {
            "build-entry.status": b"0\n", "run-entry.status": b"0\n",
            "build-positional.status": b"1\n", "run-entry.stdout": b"hello\n",
            "run-entry.stderr": b"", "build-entry.log": b"", "build-positional.log": b"",
            "command-entry.argv": b"test-only\0", "command-positional.argv": b"test-only\0",
            # Real host ELF bytes; statuses here are synthetic negative-test
            # inputs, never producer qualification.
            "out-entry.bin": Path("/bin/true").read_bytes(),
        }.items():
            (self.work / name).write_bytes(value)
        (self.work / "out-entry.bin").chmod(0o755)
        (self.work / "entry-before.sha256").write_text(receipt.digest(self.work / "out-entry.bin") + "\n")
        return snapshot

    def test_canonical_gate_emits_prospective_receipt(self):
        # A real host-native ELF is required even for this protocol-only test.
        # The fake compiler copies it; this does not qualify a Simple producer.
        payload = self.root / "hello-native"
        subprocess.run([os.environ.get("CC", "cc"), "-x", "c", "-o", str(payload), "-"],
                       input=b'#include <stdio.h>\nint main(void){puts("hello");return 0;}\n',
                       check=True, capture_output=True, timeout=30)
        self.candidate.write_text('#!/bin/sh\nset -eu\nout=""; prev=""\n'
                                  'for arg in "$@"; do\n'
                                  '  if [ "$prev" = --output ]; then out=$arg; fi\n'
                                  '  prev=$arg\ndone\n'
                                  f'cp "{payload}" "$out"\nchmod +x "$out"\n')
        self.identity["compiler_sha256"] = receipt.digest(self.candidate)
        self.identity_path.write_text(json.dumps(self.identity))
        artifacts = self.root / "artifacts"
        artifacts.mkdir()
        env = dict(os.environ, HW_ROOT=str(self.source), HW_ARTIFACT_DIR=str(artifacts),
                   HW_RECEIPT_JSON=str(self.output), HW_PRODUCER_IDENTITY_JSON=str(self.identity_path),
                   HW_PRODUCER_SOURCE_ROOT=str(self.source), HW_RUNTIME_ARCHIVE=str(self.runtime),
                   HW_BACKEND="llvm", HW_TARGET=self.identity["target"], HW_BUILD_TIMEOUT_SECONDS="5")
        result = subprocess.run(["sh", str(HERE / "check-stage2-hello-world-native-build.shs"),
                                 "--candidate", str(self.candidate)], env=env, capture_output=True, timeout=90)
        self.assertEqual(result.returncode, 0, result.stdout.decode() + result.stderr.decode())
        value = receipt.load(self.output)
        self.assertEqual(value["status"], "pass")
        self.assertEqual(value["compiler_sha256"], self.identity["compiler_sha256"])
        self.assertEqual(value["entry"]["run_exit_status"], 0)
        self.assertEqual(value["backend"], "llvm")
        self.assertEqual(value["producer_backend"], "cranelift")
        self.assertTrue((Path(value["artifact_directory"]) / "run-entry.stdout").is_file())
        self.assertEqual(value["runtime_directory"], str(self.runtime.parent))
        for form in ("entry", "positional"):
            argv = (Path(value["artifact_directory"]) / f"command-{form}.argv").read_bytes().decode().split("\0")[:-1]
            self.assertEqual(argv[argv.index("--runtime-path") + 1], str(self.runtime.parent))
            self.assertEqual(argv[argv.index("--target") + 1], self.identity["target"])

    def test_identity_mismatches_rejected(self):
        for field, value in (("compiler_sha256", "0" * 64), ("runtime_archive_sha256", "0" * 64),
                             ("source_commit", "0" * 40), ("source_tree_oid", "0" * 40),
                             ("backend", "cranelift"), ("target", "aarch64-unknown-linux-gnu")):
            with self.subTest(field=field):
                identity = dict(self.identity, **{field: value})
                self.identity_path.write_text(json.dumps(identity))
                with self.assertRaises(ValueError):
                    self.capture()
                self.assertFalse(self.output.exists())

    def test_dirty_source_rejected(self):
        self.fixture.write_text("changed")
        with self.assertRaisesRegex(ValueError, "dirty"):
            self.capture()

    def test_stale_receipt_and_duplicate_identity_rejected(self):
        self.output.write_text("historical pass")
        with self.assertRaisesRegex(ValueError, "already exists"):
            self.capture()
        self.output.unlink()
        self.identity_path.write_text('{"schema":1,"schema":2}')
        with self.assertRaisesRegex(ValueError, "duplicate"):
            self.capture()

    def test_input_mutation_between_begin_and_finish_rejected(self):
        self.artifacts()
        self.candidate.write_text("changed after begin")
        with self.assertRaisesRegex(ValueError, "candidate hash"):
            self.capture()
        self.assertFalse(self.output.exists())

    def test_failed_or_incomplete_execution_never_publishes(self):
        snapshot = self.artifacts()
        for name, data in (("run-entry.status", b"2\n"), ("build-entry.status", b"1\n"),
                           ("build-positional.status", b"139\n"), ("build-positional.status", b"124\n"),
                           ("run-entry.stdout", b"not hello\n"), ("run-entry.stdout", b"hello\nextra\n"),
                           ("run-entry.status", None), ("out-entry.bin", None)):
            with self.subTest(name=name, data=data):
                path = self.work / name
                saved = path.read_bytes()
                if data is None:
                    path.unlink()
                else:
                    path.write_bytes(data)
                with self.assertRaises((ValueError, OSError)):
                    receipt.finish(self.work, snapshot)
                self.assertFalse(self.output.exists())
                path.write_bytes(saved)
                if name == "out-entry.bin":
                    path.chmod(0o755)

    def test_executable_mutation_never_publishes(self):
        snapshot = self.artifacts()
        (self.work / "out-entry.bin").write_bytes(b"different unexecuted binary")
        with self.assertRaisesRegex(ValueError, "binary changed"):
            receipt.finish(self.work, snapshot)
        self.assertFalse(self.output.exists())

    def test_oversize_identity_rejected(self):
        self.identity_path.write_bytes(b" " * 65537)
        with self.assertRaisesRegex(ValueError, "oversize"):
            self.capture()

    def test_native_format_refuses_scripts_wrong_arch_and_unsupported_target(self):
        binary = self.root / "format-fixture"
        binary.write_bytes(b'#!/bin/sh\necho hello\n')
        with self.assertRaisesRegex(ValueError, "not a Linux ELF64"):
            receipt.native_digest(binary, self.identity["target"])
        header = bytearray(64)
        header[:7] = b"\x7fELF\x02\x01\x01"
        struct.pack_into("<HHI", header, 16, 3, 183, 1)
        binary.write_bytes(header)
        with self.assertRaisesRegex(ValueError, "architecture mismatch"):
            receipt.native_digest(binary, self.identity["target"])
        with self.assertRaisesRegex(ValueError, "unsupported"):
            receipt.native_digest(binary, "aarch64-unknown-linux-gnu")


if __name__ == "__main__":
    unittest.main()
