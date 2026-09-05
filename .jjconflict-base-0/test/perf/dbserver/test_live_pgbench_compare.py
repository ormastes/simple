#!/usr/bin/env python3
import importlib.util
import json
import os
import sys
import tempfile
import unittest
from pathlib import Path


MODULE_PATH = Path(__file__).with_name("live_pgbench_compare.py")
SPEC = importlib.util.spec_from_file_location("live_pgbench_compare", MODULE_PATH)
assert SPEC and SPEC.loader
collector = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = collector
SPEC.loader.exec_module(collector)


class PgbenchCollectorContract(unittest.TestCase):
    def test_pgbench_parser_requires_real_metrics_and_keeps_failures_retries(self):
        parsed = collector.parse_pgbench("""
number of transactions actually processed: 900
number of failed transactions: 3
number of transactions retried: 7
latency average = 2.500 ms
tps = 400.125 (without initial connection time)
""")
        self.assertEqual(parsed["transactions"], 900)
        self.assertEqual(parsed["failed"], 3)
        self.assertEqual(parsed["retried"], 7)
        self.assertEqual(parsed["latency_avg_ms"], 2.5)
        self.assertEqual(parsed["tps"], 400.125)
        with self.assertRaisesRegex(ValueError, "missing-required"):
            collector.parse_pgbench("tps = 0\nlatency average = 0 ms")
        with self.assertRaisesRegex(ValueError, "missing-required"):
            collector.parse_pgbench("number of transactions actually processed: 1\nnumber of failed transactions: 0\nlatency average = 1 ms\ntps = 1")

    def make_server(self, root: Path) -> Path:
        server = root / "admitted-simple-db"
        server.write_text("#!/bin/sh\nexec sleep 60\n")
        os.chmod(server, 0o755)
        return server

    def test_missing_targets_emit_unavailable_with_admitted_artifact_and_managed_commands(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            server = self.make_server(root)
            rc = collector.main(["--out-dir", directory, "--samples", "32", "--duration", "1", "--warmup-duration", "1", "--pgbench", "/does/not/exist", "--psql", "/does/not/exist", "--simple-artifact", str(server), "--simple-start-cmd", str(server), "--postgres-start-cmd", "/bin/sleep 60"])
            self.assertEqual(rc, 2)
            summary = json.loads((Path(directory) / "summary.json").read_text())
            self.assertEqual(summary["targets"]["postgres"], {"target": "postgres", "status": "unavailable", "reason": "missing-target-url"})
            self.assertEqual(summary["targets"]["simple"], {"target": "simple", "status": "unavailable", "reason": "missing-target-url"})
            rows = [json.loads(line) for line in (Path(directory) / "raw.jsonl").read_text().splitlines()]
            self.assertEqual([row["position"] for row in rows], list(collector.ABBA) * 8)
            self.assertTrue(all(row["status"] == "unavailable" for row in rows))

    def test_fake_commands_produce_complete_paired_abba_evidence(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            server = self.make_server(root)
            state = root / "state.json"
            fake_psql = root / "psql"
            fake_psql.write_text(f"""#!/usr/bin/env python3
import json
from pathlib import Path
import sys
state_path = Path({str(state)!r})
state = json.loads(state_path.read_text()) if state_path.exists() else {{}}
sql = sys.argv[-1]
url = next(value for value in sys.argv if value.startswith('postgres://'))
if 'DROP TABLE' in sql:
    state[url] = 0
    state_path.write_text(json.dumps(state))
if "current_setting('fsync')" in sql:
    print("on|on|on")
elif "COALESCE(sum(balance)" in sql:
    print(f"100000|{{35000350000 + state.get(url, 0) * 1000}}|96|96")
elif "SELECT 1" in sql:
    print("1")
""")
            fake_pgbench = root / "pgbench"
            fake_pgbench.write_text(f"""#!/usr/bin/env python3
import json
from pathlib import Path
import sys
state_path = Path({str(state)!r})
state = json.loads(state_path.read_text()) if state_path.exists() else {{}}
url = sys.argv[-1]
state[url] = state.get(url, 0) + 1
state_path.write_text(json.dumps(state))
print('number of transactions actually processed: 1000')
print('number of failed transactions: 0')
print('number of transactions retried: 0')
print('latency average = 1.250 ms')
print('tps = 800.000 (without initial connection time)')
""")
            os.chmod(fake_psql, 0o755)
            os.chmod(fake_pgbench, 0o755)
            out = root / "evidence"
            rc = collector.main([
                "--out-dir", str(out), "--samples", "32", "--duration", "1",
                "--warmup-duration", "1", "--postgres-url", "postgres://postgres",
                "--simple-url", "postgres://simple", "--pgbench", str(fake_pgbench),
                "--psql", str(fake_psql), "--simple-artifact", str(server),
                "--simple-start-cmd", str(server), "--postgres-start-cmd", "/bin/sleep 60",
            ])
            self.assertEqual(rc, 0)
            rows = [json.loads(line) for line in (out / "raw.jsonl").read_text().splitlines()]
            self.assertEqual([row["target"] for row in rows], list(collector.ABBA) * 8)
            self.assertTrue(all(row["status"] == "measured" for row in rows))
            summary = json.loads((out / "summary.json").read_text())
            for target in ("postgres", "simple"):
                self.assertEqual(summary["targets"][target]["samples"], 16)
                self.assertEqual(summary["targets"][target]["tps_median"], 800.0)
                self.assertEqual(summary["targets"][target]["failed"], 0)
                self.assertEqual(summary["targets"][target]["retried"], 0)
                self.assertEqual(summary["targets"][target]["resource_scope"], "managed-process-group")
                self.assertEqual(summary["targets"][target]["result_query_persistence_check"], "verified")

    def test_unrelated_simple_command_is_unavailable(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            server = self.make_server(root)
            rc = collector.main(["--out-dir", directory, "--samples", "32", "--duration", "1", "--warmup-duration", "1", "--simple-artifact", str(server), "--simple-start-cmd", "/bin/sleep 60", "--postgres-start-cmd", "/bin/sleep 60"])
            self.assertEqual(rc, 2)


if __name__ == "__main__":
    unittest.main()
