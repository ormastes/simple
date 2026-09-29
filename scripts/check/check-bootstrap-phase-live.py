#!/usr/bin/env python3
"""Host-only live service verifier; never builds, publishes, or chooses a fallback."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import queue
import re
import subprocess
import sys
import threading
import time

ROWS = ("mcp", "lsp_mcp", "spipe_plugin", "caret", "devhub", "jira", "confluence", "github")
LIMIT = 1024 * 1024
PROVIDER_ROWS = {"jira", "confluence", "github"}
PROVIDER_UNAVAILABLE_PATTERNS = (
    r"(?im)^\s*(?:error:\s*)?(?:http\s+)?(?:401|403)(?:\b|:)",
    r"(?im)^\s*(?:error:\s*)?(?:not authenticated|authentication required)\s*[.!:]?\s*$",
    r"(?im)^\s*(?:error:\s*)?(?:credentials? (?:missing|unavailable)|provider .+ not configured)\s*[.!:]?\s*$",
    r"(?im)^\s*(?:error:\s*)?(?:gh cli not found|acli not found)\s*[.!:]?\s*$",
    r"(?im)^\s*(?:error:\s*)?could not resolve host(?:\s*[:.].*)?$",
    r"(?im)^\s*(?:error:\s*)?request failed:\s*(?:network|dns|connect(?:ion|ivity)?|timeout|timed out)\b.*$",
    r"(?im)^\s*to get started with github cli, please run:\s*gh auth login\s*$",
    r"(?im)^\s*you are not logged into any github hosts\s*[.!]?\s*$",
)


class Verdict(Exception):
    def __init__(self, status, reason):
        self.status, self.reason = status, reason


def digest(path):
    with open(path, "rb") as stream:
        value = hashlib.sha256()
        for chunk in iter(lambda: stream.read(65536), b""):
            value.update(chunk)
        return value.hexdigest()


def bound_file(item):
    path = Path(item["path"])
    if not path.is_absolute():
        raise Verdict("FAIL", "artifact-path-not-absolute")
    if not path.is_file():
        raise Verdict("BLOCKED", "artifact-missing")
    if digest(path) != item["sha256"]:
        raise Verdict("FAIL", "artifact-digest-mismatch")
    return str(path)


def artifact(manifest, name):
    item = manifest.get("artifacts", {}).get(name)
    if item is None:
        raise Verdict("UNSUPPORTED", "phase-artifact-not-admitted:" + name)
    path = bound_file(item)
    # An admission receipt is supplied by the phase owner, never created here.
    admission = json.loads(Path(bound_file(item["admission"])).read_text(encoding="utf-8"))
    if (admission.get("schema") != "BootstrapPhaseArtifactAdmissionV1"
            or admission.get("phase") != manifest["phase"]
            or admission.get("status") != "ADMITTED"
            or admission.get("artifact_sha256") != item["sha256"]
            or admission.get("compiler_sha256") != manifest["compiler"]["sha256"]):
        raise Verdict("FAIL", "phase-admission-mismatch")
    bound_file(admission["evidence"])
    if name != "spipe_plugin":
        with open(path, "rb") as stream:
            if stream.read(2) == b"#!" or Path(path).suffix.lower() in (".spl", ".py", ".js", ".sh", ".shs", ".cmd", ".ps1"):
                raise Verdict("FAIL", "native-artifact-required")
    return [path]


class Child:
    """Bounded, incrementally drained pipes and a deadline, including on Windows."""
    def __init__(self, argv, env, timeout):
        self.deadline = time.monotonic() + timeout
        self.output, self.errors, self.lines = bytearray(), bytearray(), queue.Queue()
        self.overflow = False
        self.proc = subprocess.Popen(argv, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                     stderr=subprocess.PIPE, env=env,
                                     creationflags=subprocess.CREATE_NO_WINDOW if os.name == "nt" else 0)
        self.threads = []
        for pipe, target, parse in ((self.proc.stdout, self.output, True), (self.proc.stderr, self.errors, False)):
            thread = threading.Thread(target=self.drain, args=(pipe, target, parse), daemon=True)
            thread.start()
            self.threads.append(thread)

    def drain(self, pipe, target, parse):
        pending = bytearray()
        while True:
            chunk = pipe.read1(4096)
            if not chunk:
                return
            if len(target) + len(chunk) > LIMIT:
                self.overflow = True
                self.proc.kill()
                return
            target.extend(chunk)
            if parse:
                pending.extend(chunk)
                while b"\n" in pending:
                    line, _, rest = pending.partition(b"\n")
                    pending = bytearray(rest)
                    self.lines.put(line)

    def send(self, payload):
        self.proc.stdin.write(json.dumps(payload).encode() + b"\n")
        self.proc.stdin.flush()

    def response(self, request_id):
        while time.monotonic() < self.deadline:
            try:
                line = self.lines.get(timeout=min(0.1, max(0.001, self.deadline - time.monotonic())))
            except queue.Empty:
                if self.proc.poll() is not None and self.lines.empty():
                    raise Verdict("FAIL", "protocol-process-exited")
                continue
            value = json.loads(line)
            if "id" not in value:
                continue
            if value.get("jsonrpc") != "2.0" or value.get("id") != request_id:
                raise Verdict("FAIL", "protocol-response-id-mismatch")
            if "error" in value or not isinstance(value.get("result"), dict):
                raise Verdict("FAIL", "protocol-error")
            return value["result"]
        raise Verdict("BLOCKED", "protocol-timeout")

    def finish(self):
        self.proc.stdin.close()
        try:
            code = self.proc.wait(timeout=max(0.001, self.deadline - time.monotonic()))
        except subprocess.TimeoutExpired:
            raise Verdict("BLOCKED", "process-timeout")
        for thread in self.threads:
            thread.join(timeout=max(0.001, self.deadline - time.monotonic()))
        if any(thread.is_alive() for thread in self.threads):
            raise Verdict("BLOCKED", "descendant-held-pipe")
        if self.overflow:
            raise Verdict("FAIL", "output-limit-exceeded")
        return code, bytes(self.output).decode("utf-8").replace("\r\n", "\n")

    def close(self):
        if self.proc.poll() is None:
            self.proc.kill()
        self.proc.wait(timeout=5)
        # A descendant can retain a pipe after the launched process exits.
        # Closing a buffered stream while its drain thread owns the read lock
        # would block cleanup indefinitely. finish() already classifies that
        # condition as BLOCKED; daemon drains must not extend the deadline.
        pipes = [self.proc.stdin]
        if not any(thread.is_alive() for thread in self.threads):
            pipes += [self.proc.stdout, self.proc.stderr]
        for pipe in pipes:
            if pipe and not pipe.closed:
                pipe.close()


def mcp_probe(child, tool, arguments):
    child.send({"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {
        "protocolVersion": "2025-06-18", "capabilities": {},
        "clientInfo": {"name": "bootstrap-phase-live", "version": "1"}}})
    initialized = child.response(1)
    if not initialized.get("protocolVersion") or "tools" not in initialized.get("capabilities", {}):
        raise Verdict("FAIL", "mcp-tool-capability-missing")
    child.send({"jsonrpc": "2.0", "method": "notifications/initialized"})
    child.send({"jsonrpc": "2.0", "id": 2, "method": "tools/list", "params": {}})
    listing = child.response(2)
    tools = listing.get("tools")
    if not isinstance(tools, list) or not tools or any(not t.get("name") or not isinstance(t.get("inputSchema"), dict) for t in tools):
        raise Verdict("FAIL", "mcp-invalid-tool-inventory")
    if tool:
        if tool not in [t["name"] for t in tools]:
            raise Verdict("UNSUPPORTED", "mcp-required-tool-missing:" + tool)
        child.send({"jsonrpc": "2.0", "id": 3, "method": "tools/call", "params": {"name": tool, "arguments": arguments}})
        result = child.response(3)
        if result.get("isError") or not result.get("content"):
            raise Verdict("FAIL", "mcp-tool-call-failed")
    return {"tool_count": len(tools), "tool_called": tool}


def process_crashed(code):
    return code < 0 or code >= 128


def provider_unavailable(row, output):
    return row in PROVIDER_ROWS and any(
        re.search(pattern, output) for pattern in PROVIDER_UNAVAILABLE_PATTERNS
    )


def require_provider_process(row, code, output, failure_reason, crash_reason):
    if process_crashed(code):
        raise Verdict("FAIL", crash_reason)
    if code:
        if provider_unavailable(row, output):
            raise Verdict("BLOCKED", "provider-auth-or-connectivity-unavailable")
        raise Verdict("FAIL", failure_reason)
    if provider_unavailable(row, output):
        raise Verdict("BLOCKED", "provider-auth-or-connectivity-unavailable")


def parse_provider(row, output, code, expected, errors=""):
    # Never include server bodies or credentials in receipts.
    require_provider_process(
        row, code, output + "\n" + errors,
        "provider-command-failed", "provider-process-crashed",
    )
    if row == "jira":
        value = json.loads(output)
        valid = value.get("key") == expected and bool(value.get("id")) and isinstance(value.get("fields"), dict)
    elif row == "confluence":
        value = json.loads(output)
        valid = str(value.get("id")) == expected and bool(value.get("title"))
    else:
        value = json.loads(output)
        valid = value.get("nameWithOwner", "").lower() == expected.lower() and bool(value.get("url"))
    if not valid:
        raise Verdict("FAIL", "provider-resource-response-mismatch")


def provider_identity(manifest, row, argv, env, timeout, receipt):
    resources = manifest.get("resources", {})
    principal = resources.get(row + "_principal")
    if not principal:
        raise Verdict("BLOCKED", "expected-authenticated-principal-not-configured:" + row)
    if row == "jira":
        identity_argv = argv[:1] + ["api", "GET", "/myself", "--jira", "--include"]
        identity_key = "accountId"
    elif row == "confluence":
        endpoint = resources.get("confluence_identity_url", "")
        if not endpoint.startswith("https://") or not endpoint.endswith("/rest/api/user/current"):
            raise Verdict("BLOCKED", "confluence-current-user-endpoint-not-configured")
        identity_argv = argv[:1] + ["api", "GET", endpoint, "--include"]
        identity_key = "accountId"
    else:
        if "github_cli" not in manifest:
            raise Verdict("BLOCKED", "github-reference-cli-not-bound")
        identity_argv = [bound_file(manifest["github_cli"]), "api", "user"]
        identity_key = "login"
    child = Child(identity_argv, env, timeout)
    receipt["identity_launched"] = True
    receipt["identity_argv"] = identity_argv
    try:
        code, output = child.finish()
        errors = bytes(child.errors).decode("utf-8", errors="replace").replace("\r\n", "\n")
        require_provider_process(
            row, code, output + "\n" + errors,
            "identity-command-failed", "identity-process-crashed",
        )
        if row != "github":
            if not output.startswith("HTTP 200\n"):
                raise Verdict("FAIL", "identity-http-status-invalid")
            output = output.split("\n", 1)[1].strip()
        value = json.loads(output)
        if value.get(identity_key) != principal:
            raise Verdict("FAIL", "authenticated-principal-mismatch")
        receipt["principal_sha256"] = hashlib.sha256(principal.encode()).hexdigest()
    finally:
        child.close()
        receipt["identity_stdout_sha256"] = hashlib.sha256(child.output).hexdigest()
        receipt["identity_stderr_sha256"] = hashlib.sha256(child.errors).hexdigest()


def probe(manifest, row, env, timeout, receipt):
    name = "devhub" if row in ("jira", "confluence", "github") else row
    argv = artifact(manifest, name)
    receipt["artifact_sha256"] = manifest["artifacts"][name]["sha256"]
    tool, arguments = None, {}
    if row == "mcp":
        tool, arguments = "simple_search", {"query": "__BOOTSTRAP_PHASE_LIVE_NO_MATCH__", "scope": "src"}
    elif row == "caret":
        tool = "chat_who"
    elif row == "spipe_plugin":
        plugin = bound_file(manifest["spipe_plugin_entry"])
        receipt["plugin_sha256"] = manifest["spipe_plugin_entry"]["sha256"]
        argv += [plugin, "self-review-guide"]
    elif row == "devhub":
        argv += ["--help"]
    elif row in ("jira", "confluence", "github"):
        expected = manifest.get("resources", {}).get(row)
        if not expected:
            raise Verdict("BLOCKED", "readable-resource-not-configured:" + row)
        provider_identity(manifest, row, argv, env, timeout, receipt)
        if row == "jira":
            argv += ["jira", "view", expected, "--json"]
        elif row == "confluence":
            argv += ["wiki", "view", expected, "--backend", "confluence", "--json"]
        else:
            argv += ["github", "repo", "view", expected, "--json", "nameWithOwner,url"]
    receipt["argv"] = argv
    child = Child(argv, env, timeout)
    receipt["launched"] = True
    receipt["pid"] = child.proc.pid
    try:
        if row in ("mcp", "lsp_mcp", "caret"):
            receipt.update(mcp_probe(child, tool, arguments))
        code, output = child.finish()
        receipt["exit_code"] = code
        if row in ("jira", "confluence", "github"):
            errors = bytes(child.errors).decode("utf-8", errors="replace").replace("\r\n", "\n")
            parse_provider(row, output, code, expected, errors)
        elif code:
            raise Verdict("FAIL", "process-nonzero-exit")
        elif row == "devhub" and not all(word in output.lower() for word in ("jira", "wiki", "github", "auth")):
            raise Verdict("FAIL", "devhub-dispatch-inventory-missing")
        elif row == "spipe_plugin" and (len(output.strip()) < 40 or "self-review" not in output.lower()):
            raise Verdict("FAIL", "spipe-plugin-guide-invalid")
        if any(marker in output.lower() for marker in ("native_missing", "stub fallback", "source fallback")):
            raise Verdict("FAIL", "fallback-observed")
    finally:
        child.close()
        receipt["stdout_sha256"] = hashlib.sha256(child.output).hexdigest()
        receipt["stderr_sha256"] = hashlib.sha256(child.errors).hexdigest()
    artifact(manifest, name)  # detects mutation during launch
    if row == "spipe_plugin":
        bound_file(manifest["spipe_plugin_entry"])
    if row == "github":
        bound_file(manifest["github_cli"])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", required=True)
    parser.add_argument("--output", required=True)
    parser.add_argument("--timeout", type=int, default=30)
    parser.add_argument("--row", choices=ROWS)
    parser.add_argument("--expect-phase", type=int)
    parser.add_argument("--expect-cli")
    parser.add_argument("--expect-mcp")
    parser.add_argument("--expect-lsp")
    parser.add_argument("--credential-home")
    args = parser.parse_args()
    if args.timeout < 1 or args.timeout > 300:
        parser.error("timeout must be 1..300 seconds")
    manifest_path = Path(args.manifest).resolve()
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    manifest_hash = digest(manifest_path)
    if manifest.get("schema") != "BootstrapPhaseLiveManifestV1" or manifest.get("phase") not in (1, 2, 3, 4, 5):
        parser.error("invalid phase manifest")
    if args.expect_phase is not None and manifest["phase"] != args.expect_phase:
        parser.error("phase does not match invoking matrix")
    for expected, item in ((args.expect_cli, manifest["compiler"]),
                           (args.expect_mcp, manifest.get("artifacts", {}).get("mcp")),
                           (args.expect_lsp, manifest.get("artifacts", {}).get("lsp_mcp"))):
        if expected and (not item or Path(expected).resolve() != Path(item["path"]).resolve()
                         or digest(expected) != item["sha256"]):
            parser.error("artifact does not match invoking matrix")
    output = Path(args.output).resolve()
    output.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, SIMPLE_NO_STUB_FALLBACK="1", SIMPLE_MCP_ALLOW_SOURCE_FALLBACK="0", SIMPLE_MCP_TOOL_SET="all", NO_COLOR="1", GH_PROMPT_DISABLED="1")
    if args.credential_home:
        env["HOME"] = str(Path(args.credential_home).resolve())
    # Auth stays in the operator's credential home. No tokens enter the manifest.
    results = []
    for row in ((args.row,) if args.row else ROWS):
        destination = output / (row + ".json")
        if destination.exists():
            parser.error("receipt exists; choose a new output directory before launching")
        receipt = {"schema": "BootstrapPhaseLiveReceiptV1", "phase": manifest["phase"],
                   "row": row, "manifest_sha256": manifest_hash, "launched": False,
                   "resume_argv": [sys.executable, str(Path(__file__).resolve()), "--manifest", str(manifest_path), "--output", str(output.parent / (output.name + "-resume-" + row)), "--timeout", str(args.timeout), "--row", row]}
        started = time.monotonic()
        try:
            compiler = bound_file(manifest["compiler"])
            env.update(SIMPLE_BINARY=compiler, SIMPLE_BIN=compiler)
            probe(manifest, row, env, args.timeout, receipt)
            bound_file(manifest["compiler"])
            if digest(manifest_path) != manifest_hash:
                raise Verdict("FAIL", "manifest-drift")
            receipt.update(status="PASS", reason="live-response-validated")
        except Verdict as error:
            receipt.update(status=error.status, reason=error.reason)
        except (OSError, ValueError, KeyError, TypeError, AttributeError, subprocess.SubprocessError) as error:
            receipt.update(status="FAIL", reason="probe-invalid:" + type(error).__name__)
        receipt["elapsed_ms"] = round((time.monotonic() - started) * 1000)
        destination.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
        results.append(receipt["status"])
        print(row + "=" + receipt["status"] + ":" + receipt["reason"])
    return 1 if "FAIL" in results else (2 if any(result != "PASS" for result in results) else 0)


if __name__ == "__main__":
    sys.exit(main())
