"""Controller tests only: fixtures never count as live bootstrap acceptance."""
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[3]
SPEC = importlib.util.spec_from_file_location("phase_live", ROOT / "scripts/check/check-bootstrap-phase-live.py")
LIVE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(LIVE)


class PhaseLiveContract(unittest.TestCase):
    def test_provider_usage_words_do_not_mask_failure_but_exact_unauthorized_blocks(self):
        usage = "Usage: devhub auth login --token TOKEN\nrequest failed: http parser panic\n"
        with self.assertRaises(LIVE.Verdict) as failure:
            LIVE.parse_provider("github", usage, 1, "org/repo")
        self.assertEqual(failure.exception.status, "FAIL")
        self.assertEqual(failure.exception.reason, "provider-command-failed")
        with self.assertRaises(LIVE.Verdict) as unavailable:
            LIVE.parse_provider("github", "HTTP 401\n", 1, "org/repo")
        self.assertEqual(unavailable.exception.status, "BLOCKED")

    def test_provider_crash_precedes_unauthorized_classification(self):
        with self.assertRaises(LIVE.Verdict) as result:
            LIVE.parse_provider("github", "HTTP 401\n", 139, "org/repo")
        self.assertEqual(result.exception.status, "FAIL")
        self.assertEqual(result.exception.reason, "provider-process-crashed")

    def test_identity_command_failure_is_not_auth_unavailability(self):
        class FailingIdentityChild:
            def __init__(self, argv, env, timeout):
                self.output = bytearray(b"identity implementation failure\n")
                self.errors = bytearray()

            def finish(self):
                return 1, self.output.decode()

            def close(self):
                pass

        manifest = {
            "resources": {"github_principal": "fixture-user"},
            "github_cli": {"path": str(Path(sys.executable).resolve()),
                           "sha256": LIVE.digest(sys.executable)},
        }
        with mock.patch.object(LIVE, "Child", FailingIdentityChild):
            with self.assertRaises(LIVE.Verdict) as result:
                LIVE.provider_identity(manifest, "github", ["unused"], {}, 1, {})
        self.assertEqual(result.exception.status, "FAIL")
        self.assertEqual(result.exception.reason, "identity-command-failed")

    def test_provider_expected_identity_is_required(self):
        with self.assertRaises(LIVE.Verdict) as result:
            LIVE.provider_identity({}, "jira", ["unused"], {}, 1, {})
        self.assertEqual(result.exception.status, "BLOCKED")

    def test_provider_ids_and_error_json_are_checked(self):
        LIVE.parse_provider("jira", '{"key":"X-1","id":"1","fields":{}}', 0, "X-1")
        LIVE.parse_provider("confluence", '{"id":"42","title":"Probe"}', 0, "42")
        LIVE.parse_provider("github", '{"nameWithOwner":"org/repo","url":"https://github.com/org/repo"}', 0, "org/repo")
        for row in ("jira", "confluence", "github"):
            with self.assertRaises(LIVE.Verdict):
                LIVE.parse_provider(row, '{"error":"denied"}', 0, "X-1")
        with self.assertRaises(LIVE.Verdict) as result:
            LIVE.parse_provider("jira", "HTTP 401 secret-body", 1, "X-1")
        self.assertEqual(result.exception.status, "BLOCKED")
        self.assertNotIn("secret-body", result.exception.reason)

    def test_unadmitted_artifact_is_unsupported(self):
        with self.assertRaises(LIVE.Verdict) as result:
            LIVE.artifact({"artifacts": {}}, "mcp")
        self.assertEqual(result.exception.status, "UNSUPPORTED")

    def test_changed_file_is_rejected(self):
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder) / "file"
            path.write_bytes(b"first")
            binding = {"path": str(path), "sha256": LIVE.digest(path)}
            LIVE.bound_file(binding)
            path.write_bytes(b"changed")
            with self.assertRaises(LIVE.Verdict) as result:
                LIVE.bound_file(binding)
            self.assertEqual(result.exception.status, "FAIL")

    def test_mcp_interactive_protocol(self):
        source = '''import json,sys
for line in sys.stdin:
    request=json.loads(line)
    if "id" not in request: continue
    method=request["method"]
    if method=="initialize": result={"protocolVersion":"2025-06-18","capabilities":{"tools":{}}}
    elif method=="tools/list": result={"tools":[{"name":"chat_who","inputSchema":{"type":"object"}}]}
    else: result={"content":[{"type":"text","text":"[]"}]}
    print(json.dumps({"jsonrpc":"2.0","id":request["id"],"result":result}),flush=True)
'''
        with tempfile.TemporaryDirectory() as folder:
            fixture = Path(folder) / "fixture.py"
            fixture.write_text(source)
            child = LIVE.Child([sys.executable, str(fixture)], os.environ.copy(), 5)
            try:
                self.assertEqual(LIVE.mcp_probe(child, "chat_who", {})["tool_called"], "chat_who")
                self.assertEqual(child.finish()[0], 0)
            finally:
                child.close()

    def test_mcp_error_and_wrong_id_fail(self):
        for body in ({"jsonrpc":"2.0","id":7,"result":{}}, {"jsonrpc":"2.0","id":1,"error":{"code":-1}}):
            with tempfile.TemporaryDirectory() as folder:
                fixture = Path(folder) / "fixture.py"
                fixture.write_text("import json\nprint(" + repr(json.dumps(body)) + ",flush=True)\n")
                child = LIVE.Child([sys.executable, str(fixture)], os.environ.copy(), 5)
                try:
                    with self.assertRaises(LIVE.Verdict):
                        child.response(1)
                finally:
                    child.close()

    def test_empty_phase_records_every_unavailable_row(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            driver = root / "driver"
            driver.write_bytes(b"controller fixture only")
            manifest = root / "manifest.json"
            manifest.write_text(json.dumps({"schema":"BootstrapPhaseLiveManifestV1", "phase":2,
                "compiler":{"path":str(driver),"sha256":LIVE.digest(driver)}, "artifacts":{}}))
            command = [sys.executable, str(ROOT / "scripts/check/check-bootstrap-phase-live.py"),
                       "--manifest", str(manifest), "--output", str(root / "receipts")]
            result = subprocess.run(command, capture_output=True, text=True, timeout=10)
            self.assertEqual(result.returncode, 2, result.stderr)
            receipts = [json.loads(path.read_text()) for path in (root / "receipts").glob("*.json")]
            self.assertEqual(len(receipts), len(LIVE.ROWS))
            self.assertTrue(all(row["status"] == "UNSUPPORTED" and not row["launched"] for row in receipts))
            self.assertTrue(all(row["resume_argv"] for row in receipts))

    def test_stage4_requires_live_services(self):
        matrix = (ROOT / "scripts/bootstrap/stage4-tooling-matrix.shs").read_text()
        self.assertIn("printf 'phase_live_services\\trequired\\t", matrix)
        self.assertIn("--expect-phase 4 --expect-cli", matrix)
        self.assertIn("phase-live-service-unavailable", matrix)


if __name__ == "__main__":
    unittest.main()
