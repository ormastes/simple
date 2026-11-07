#!/usr/bin/env python3
"""Parser/statistic regressions only; synthetic records are not app evidence."""
import importlib.util
from pathlib import Path
import tempfile
import unittest
import json

spec = importlib.util.spec_from_file_location("matched", Path(__file__).with_name("run-item5-matched-app-performance.py"))
matched = importlib.util.module_from_spec(spec)
spec.loader.exec_module(matched)


class MeasurementContract(unittest.TestCase):
    def record(self, content, kind="db", size=1025, vector=True):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "stdout"
            path.write_text(content)
            return matched.sample_record(path, kind, size, vector)

    def text(self, extra="", **changes):
        values = dict(kind="db", size=1025, operations=32, ns=100, checksum=123,
                      results=4, provider_calls=32, warmups=3)
        values.update(changes)
        return "ITEM5_PERF_V1 " + " ".join(f"{k}={v}" for k, v in values.items()) + extra + "\n"

    def test_nearest_rank_30_and_100(self):
        self.assertEqual(matched.percentile(list(range(1, 31)), 50), 15)
        self.assertEqual(matched.percentile(list(range(1, 31)), 95), 29)
        self.assertEqual(matched.percentile(list(range(1, 101)), 95), 95)

    def test_provider_staged_in_admitted_relative_root(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "original.so"
            source.write_bytes(b"component fixture; not an executable provider")
            output = root / "output"
            output.mkdir()
            expected = matched.digest(source)
            argument, staged = matched.stage_provider(source, output, expected)
            self.assertEqual(argument.as_posix(), "build/providers/matched-provider.so")
            self.assertFalse(argument.is_absolute())
            self.assertEqual(staged, output / argument)
            self.assertEqual(matched.digest(staged), expected)
            source.write_bytes(b"changed input")
            other = root / "other-output"
            other.mkdir()
            with self.assertRaises(ValueError):
                matched.stage_provider(source, other, expected)

    def test_exact_one_measured_sample(self):
        self.assertEqual(self.record(self.text())["operations"], 32)
        with self.assertRaises(ValueError):
            self.record(self.text() + self.text())

    def test_duplicate_field_rejected(self):
        with self.assertRaises(ValueError):
            self.record(self.text(" ns=200"))

    def test_cache_bypass_or_scalar_provider_use_rejected(self):
        with self.assertRaises(ValueError):
            self.record(self.text(provider_calls=31))
        with self.assertRaises(ValueError):
            self.record(self.text(), vector=False)

    def test_wrong_workload_or_zero_time_rejected(self):
        for changes in ({"size": 65536}, {"operations": 31}, {"ns": 0}, {"warmups": 2}):
            with self.subTest(changes=changes), self.assertRaises(ValueError):
                self.record(self.text(**changes))

    def test_http_requires_full_wire(self):
        record = self.text(kind="http", size=128, operations=128, results=128, provider_calls=128)
        with self.assertRaises(ValueError):
            self.record(record, kind="http", size=128)
        wire = b"HTTP/1.1 200 OK\r\nContent-Length: 23\r\n\r\nITEM5_MATCHED_HTTP_BODY"
        result = self.record(record + "ITEM5_PERF_WIRE_V1 hex=" + wire.hex() + "\n", kind="http", size=128)
        self.assertEqual(result["wire_hex"], wire.hex())

    def test_functional_gate_rejects_hash_only_manifest(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "evidence.env"
            path.write_text("schema=hashes-only\nqualification=pass\n")
            with self.assertRaises(ValueError):
                matched.functional_gate(path, {})

    def test_functional_gate_rejects_failed_or_nonquiescent_app(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "staged").mkdir()
            (root / "receipts").mkdir()
            hello = root / "staged/producer-hello.json"
            hello.write_text(json.dumps({"runtime_archive_sha256": "runtime"}))
            evidence = root / "evidence.env"
            evidence.write_text("schema=item5-app-vector-runner-v1\nqualification=execution-evidence-only\n"
                                "producer_compiler_sha256=compiler\nproducer_source_commit=producer\n"
                                "app_source_commit=source\nprovider_identity=1\nimplementation_identity=2\n"
                                "producer_hello_receipt_sha256=" + matched.digest(hello) + "\n")
            m = {"compiler": {"sha256": "compiler"}, "runtime": {"sha256": "runtime"},
                 "producer_source_commit": "producer", "functional_app_source_commit": "source",
                 "provider_id": 1, "implementation_id": 2}
            for body in ("status=complete\nexit_status=1\nquiescent=1\n",
                         "status=complete\nexit_status=0\nquiescent=0\n"):
                (root / "receipts/db-scalar.rss.env").write_text(body)
                with self.assertRaises(ValueError):
                    matched.functional_gate(evidence, m)


if __name__ == "__main__":
    unittest.main()
