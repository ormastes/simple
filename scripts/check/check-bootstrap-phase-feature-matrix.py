#!/usr/bin/env python3
"""Run the fixed Phase 1/2 feature matrix from exact admitted artifacts only."""

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


SUITE_FAMILIES = (
    "compiler",
    "language_runtime",
    "simple_mcp",
    "simple_lsp_mcp",
    "t32_mcp",
    "spipe_sspec",
    "caret",
    "slang",
    "simd_db_web",
    "devhub",
)
ROWS = tuple(
    row
    for family in SUITE_FAMILIES
    for row in (family + "_interpreter", family + "_native")
) + (
    "simple_mcp_protocol",
    "simple_lsp_mcp_protocol",
    "t32_mcp_protocol",
    "spipe_plugin_launch",
    "caret_protocol",
    "slang_binary_launch",
    "devhub_launch",
    "devhub_github",
    "devhub_jira",
    "devhub_confluence",
)
OUTPUT_LIMIT = 1024 * 1024
SCRIPT_SUFFIXES = {".spl", ".py", ".js", ".sh", ".shs", ".cmd", ".ps1"}
PROVIDER_ROWS = {"devhub_github", "devhub_jira", "devhub_confluence"}
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
        self.status = status
        self.reason = reason


def digest(path):
    value = hashlib.sha256()
    with open(path, "rb") as stream:
        for chunk in iter(lambda: stream.read(65536), b""):
            value.update(chunk)
    return value.hexdigest()


def canonical_digest(value):
    data = json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(data).hexdigest()


def env_receipt(path):
    values = {}
    for line in Path(path).read_text(encoding="utf-8").splitlines():
        if not line or line.startswith("#"):
            continue
        if "=" not in line:
            raise Verdict("FAIL", "authority-receipt-invalid")
        key, value = line.split("=", 1)
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", key) or key in values:
            raise Verdict("FAIL", "authority-receipt-invalid")
        values[key] = value
    return values


def bound_file(item, *, native=False):
    if not isinstance(item, dict) or not item.get("path") or not item.get("sha256"):
        raise Verdict("FAIL", "artifact-binding-incomplete")
    path = Path(item["path"])
    if not path.is_absolute():
        raise Verdict("FAIL", "artifact-path-not-absolute")
    if path.is_symlink():
        raise Verdict("FAIL", "artifact-symlink-rejected")
    if not path.is_file():
        raise Verdict("BLOCKED", "artifact-missing")
    if digest(path) != item["sha256"]:
        raise Verdict("FAIL", "artifact-digest-mismatch")
    if native:
        with open(path, "rb") as stream:
            prefix = stream.read(2)
        if prefix == b"#!" or path.suffix.lower() in SCRIPT_SUFFIXES:
            raise Verdict("FAIL", "native-executable-required")
    return str(path.resolve())


def validate_manifest(manifest):
    if manifest.get("schema") != "BootstrapPhaseFeatureManifestV1":
        raise Verdict("FAIL", "manifest-schema-invalid")
    if manifest.get("phase") not in (1, 2):
        raise Verdict("FAIL", "phase-must-be-one-or-two")
    if not isinstance(manifest.get("generation"), str) or not manifest["generation"].strip():
        raise Verdict("FAIL", "generation-missing")
    jobs = manifest.get("bootstrap_jobs", {})
    selected = jobs.get("selected")
    detected = jobs.get("detected_cpu_count")
    if not isinstance(selected, int) or not isinstance(detected, int) or selected < 1 or detected < 1:
        raise Verdict("FAIL", "bootstrap-job-counts-invalid")
    if not isinstance(manifest.get("compiler"), dict):
        raise Verdict("FAIL", "compiler-binding-missing")
    capabilities = manifest.get("capability_set")
    if (
        not isinstance(capabilities, list) or not capabilities
        or any(not isinstance(value, str) or not value for value in capabilities)
        or capabilities != sorted(set(capabilities))
    ):
        raise Verdict("FAIL", "capability-set-invalid")
    if not isinstance(manifest.get("rows", {}), dict):
        raise Verdict("FAIL", "rows-must-be-object")
    if manifest["phase"] == 1 and not isinstance(manifest.get("current_authority"), dict):
        raise Verdict("FAIL", "phase1-current-authority-missing")
    if manifest["phase"] == 1 and not isinstance(manifest.get("handoff"), dict):
        raise Verdict("FAIL", "phase1-handoff-missing")


def validate_phase1_handoff(manifest):
    if manifest["phase"] != 1:
        return None
    binding = manifest["handoff"]
    handoff_path = bound_file(binding)
    try:
        handoff = json.loads(Path(handoff_path).read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError):
        raise Verdict("FAIL", "phase1-handoff-invalid")
    compiler_path = str(Path(manifest["compiler"].get("path", "")).resolve())
    marker_path = str(Path(manifest["current_authority"].get("path", "")).resolve())
    expected = {
        "schema": "simple-bootstrap-phase1-current-handoff-v1",
        "status": "current-committed",
        "artifact_path": compiler_path,
        "artifact_sha256": manifest["compiler"].get("sha256"),
        "admission_path": marker_path,
        "admission_sha256": manifest["current_authority"].get("sha256"),
        "generation": manifest["generation"],
        "selected_jobs": manifest["bootstrap_jobs"]["selected"],
        "detected_available_cpus": manifest["bootstrap_jobs"]["detected_cpu_count"],
    }
    for key, value in expected.items():
        actual = handoff.get(key)
        if key.endswith("_path") and actual:
            actual = str(Path(actual).resolve())
        if actual != value:
            raise Verdict("FAIL", "phase1-handoff-mismatch:" + key)
    stamp_path = bound_file({"path": handoff.get("stamp_path"), "sha256": handoff.get("stamp_sha256")})
    if not stamp_path.endswith(".inputs.sha256"):
        raise Verdict("FAIL", "phase1-handoff-stamp-invalid")
    return {"path": handoff_path, "sha256": binding["sha256"], "stamp_path": stamp_path}


def validate_current_phase_authority(manifest):
    if manifest["phase"] != 1:
        return None
    binding = manifest["current_authority"]
    marker_path = bound_file(binding)
    marker = Path(marker_path)
    if marker.name != "bootstrap.current.env" or os.path.lexists(str(marker) + ".transaction"):
        raise Verdict("FAIL", "phase1-current-authority-not-stable")
    values = env_receipt(marker)
    generation = values.get("generation", "")
    if (
        values.get("schema") != "simple-bootstrap-authority-current-v1"
        or generation != manifest["generation"]
        or not re.fullmatch(r"[A-Za-z0-9._-]+", generation)
    ):
        raise Verdict("FAIL", "phase1-current-generation-mismatch")
    generation_dir = marker.parent / "bootstrap.generations" / generation
    if not generation_dir.is_dir() or generation_dir.is_symlink():
        raise Verdict("FAIL", "phase1-generation-directory-invalid")
    stamps = list(generation_dir.glob("*.inputs.sha256"))
    if len(stamps) != 1 or stamps[0].is_symlink():
        raise Verdict("FAIL", "phase1-seed-stamp-ambiguous")
    stamp = stamps[0]
    stamp_values = env_receipt(stamp)
    seed = Path(str(stamp)[:-len(".inputs.sha256")])
    if (
        stamp_values.get("schema") != "simple-bootstrap-seed-artifact-stamp-v2"
        or stamp_values.get("inputs_fingerprint") != values.get("inputs_fingerprint")
        or digest(stamp) != values.get("stamp_sha256")
        or not seed.is_file() or seed.is_symlink()
        or digest(seed) != manifest["compiler"].get("sha256")
        or stamp_values.get("seed_sha256") != manifest["compiler"].get("sha256")
    ):
        raise Verdict("FAIL", "phase1-current-seed-mismatch")
    return {
        "path": marker_path,
        "sha256": binding["sha256"],
        "stamp_path": str(stamp.resolve()),
        "stamp_sha256": digest(stamp),
        "admitted_compiler_path": str(seed.resolve()),
        "admitted_compiler_sha256": digest(seed),
    }


def artifact_item(manifest, name):
    if name == "compiler":
        return manifest["compiler"]
    item = manifest.get("artifacts", {}).get(name)
    if item is None:
        raise Verdict("UNSUPPORTED", "phase-artifact-not-admitted:" + name)
    return item


def admitted_artifact(manifest, name):
    item = artifact_item(manifest, name)
    if item.get("generation") != manifest["generation"]:
        raise Verdict("FAIL", "stale-artifact-generation:" + name)
    path = bound_file(item, native=True)
    provenance = item.get("provenance")
    admission_binding = item.get("admission")
    provenance_path = bound_file(provenance)
    admission_path = bound_file(admission_binding)
    if manifest["phase"] == 1 and name == "compiler":
        handoff = validate_phase1_handoff(manifest)
        if provenance_path != handoff["path"] or admission_path != handoff["path"]:
            raise Verdict("FAIL", "phase1-compiler-must-bind-exact-handoff")
        admission = None
    else:
        try:
            admission = json.loads(Path(admission_path).read_text(encoding="utf-8"))
        except (OSError, UnicodeError, json.JSONDecodeError):
            raise Verdict("FAIL", "artifact-admission-invalid:" + name)
    compiler_sha = manifest["compiler"].get("sha256")
    expected = {
        "schema": "BootstrapPhaseFeatureAdmissionV1",
        "phase": manifest["phase"],
        "generation": manifest["generation"],
        "status": "ADMITTED",
        "artifact_path": path,
        "artifact_sha256": item["sha256"],
        "compiler_sha256": compiler_sha,
        "provenance_sha256": provenance["sha256"],
        "capability_set_sha256": canonical_digest(manifest["capability_set"]),
    }
    if admission is not None:
        for key, value in expected.items():
            actual = admission.get(key)
            if key == "artifact_path" and actual:
                actual = str(Path(actual).resolve())
            if actual != value:
                raise Verdict("FAIL", "artifact-admission-mismatch:" + name + ":" + key)
    return {
        "name": name,
        "path": path,
        "sha256": item["sha256"],
        "generation": item["generation"],
        "provenance_path": provenance_path,
        "provenance_sha256": provenance["sha256"],
        "admission_path": admission_path,
        "admission_sha256": admission_binding["sha256"],
    }


def validate_row_pin(row, artifact):
    expected = {
        "artifact_sha256": artifact["sha256"],
        "generation": artifact["generation"],
        "provenance_sha256": artifact["provenance_sha256"],
        "admission_sha256": artifact["admission_sha256"],
    }
    for key, value in expected.items():
        if row.get(key) != value:
            raise Verdict("FAIL", "stale-row-artifact-pin:" + key)


def validate_row_shape(row_name, row):
    if not row.get("owner") or not row.get("reviewer"):
        raise Verdict("FAIL", "row-owner-reviewer-missing")
    support = row.get("support")
    if support in ("unsupported", "blocked"):
        if not row.get("reason") or not row.get("owner") or not row.get("prerequisite"):
            raise Verdict("FAIL", "unavailable-row-metadata-incomplete")
        return
    if support != "supported":
        raise Verdict("FAIL", "row-support-state-invalid")
    if row_name.endswith("_interpreter"):
        if row.get("kind") != "suite" or row.get("mode") != "interpreter":
            raise Verdict("FAIL", "interpreter-row-shape-invalid")
    elif row_name.endswith("_native"):
        if row.get("kind") != "suite" or row.get("mode") != "native":
            raise Verdict("FAIL", "native-row-shape-invalid")
    elif row_name.endswith("_protocol"):
        expected_tools = row.get("expected_tools")
        if (
            row.get("kind") != "mcp" or not isinstance(expected_tools, list)
            or not expected_tools or any(not isinstance(value, str) or not value for value in expected_tools)
        ):
            raise Verdict("FAIL", "protocol-row-shape-invalid")
    elif row_name in (
        "spipe_plugin_launch", "slang_binary_launch", "devhub_launch",
        "devhub_github", "devhub_jira", "devhub_confluence",
    ):
        markers = row.get("expected_stdout")
        if (
            row.get("kind") != "command" or not isinstance(markers, list)
            or not markers or any(not isinstance(value, str) or not value for value in markers)
        ):
            raise Verdict("FAIL", "command-row-shape-invalid")
        if row_name == "spipe_plugin_launch" and not row.get("inputs"):
            raise Verdict("FAIL", "spipe-plugin-entry-binding-missing")


def validate_inventory(row):
    tests = row.get("tests")
    if not isinstance(tests, list) or not tests:
        raise Verdict("FAIL", "suite-inventory-empty")
    inventory = []
    for test in tests:
        inventory.append({"path": bound_file(test), "sha256": test["sha256"]})
    inventory.sort(key=lambda item: item["path"])
    return inventory


class Child:
    def __init__(self, argv, env, timeout):
        self.deadline = time.monotonic() + timeout
        self.stdout = bytearray()
        self.stderr = bytearray()
        self.lines = queue.Queue()
        self.overflow = False
        self.proc = subprocess.Popen(
            argv,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env=env,
            creationflags=subprocess.CREATE_NO_WINDOW if os.name == "nt" else 0,
        )
        self.threads = []
        for pipe, target, parse in (
            (self.proc.stdout, self.stdout, True),
            (self.proc.stderr, self.stderr, False),
        ):
            thread = threading.Thread(target=self._drain, args=(pipe, target, parse), daemon=True)
            thread.start()
            self.threads.append(thread)

    def _drain(self, pipe, target, parse):
        pending = bytearray()
        while True:
            chunk = pipe.read1(4096)
            if not chunk:
                return
            if len(target) + len(chunk) > OUTPUT_LIMIT:
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
            try:
                value = json.loads(line)
            except json.JSONDecodeError:
                raise Verdict("FAIL", "protocol-output-not-json")
            if "id" not in value:
                continue
            if value.get("jsonrpc") != "2.0" or value.get("id") != request_id:
                raise Verdict("FAIL", "protocol-response-id-mismatch")
            if "error" in value or not isinstance(value.get("result"), dict):
                raise Verdict("FAIL", "protocol-error")
            return value["result"]
        raise Verdict("BLOCKED", "protocol-timeout")

    def finish(self):
        if self.proc.stdin and not self.proc.stdin.closed:
            self.proc.stdin.close()
        try:
            code = self.proc.wait(timeout=max(0.001, self.deadline - time.monotonic()))
        except subprocess.TimeoutExpired:
            self.proc.kill()
            self.proc.wait(timeout=5)
            raise Verdict("BLOCKED", "process-timeout")
        for thread in self.threads:
            thread.join(timeout=max(0.001, self.deadline - time.monotonic()))
        if any(thread.is_alive() for thread in self.threads):
            raise Verdict("BLOCKED", "descendant-held-pipe")
        if self.overflow:
            raise Verdict("FAIL", "output-limit-exceeded")
        return code, self.stdout.decode("utf-8", errors="replace").replace("\r\n", "\n")

    def close(self):
        if self.proc.poll() is None:
            self.proc.kill()
            self.proc.wait(timeout=5)


def mcp_probe(child, row):
    child.send({"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {
        "protocolVersion": "2025-06-18",
        "capabilities": {},
        "clientInfo": {"name": "bootstrap-phase-feature-matrix", "version": "1"},
    }})
    initialized = child.response(1)
    if not initialized.get("protocolVersion") or "tools" not in initialized.get("capabilities", {}):
        raise Verdict("FAIL", "mcp-tool-capability-missing")
    child.send({"jsonrpc": "2.0", "method": "notifications/initialized"})
    child.send({"jsonrpc": "2.0", "id": 2, "method": "tools/list", "params": {}})
    listing = child.response(2)
    tools = listing.get("tools")
    if not isinstance(tools, list) or not tools:
        raise Verdict("FAIL", "mcp-tool-inventory-empty")
    if any(
        not isinstance(tool, dict) or not tool.get("name")
        or not isinstance(tool.get("inputSchema"), dict)
        for tool in tools
    ):
        raise Verdict("FAIL", "mcp-tool-inventory-invalid")
    names = [tool["name"] for tool in tools]
    for expected in row.get("expected_tools", []):
        if expected not in names:
            raise Verdict("FAIL", "mcp-required-tool-missing:" + expected)
    call = row.get("call")
    if call:
        if call.get("tool") not in names or not isinstance(call.get("arguments", {}), dict):
            raise Verdict("FAIL", "mcp-call-contract-invalid")
        child.send({"jsonrpc": "2.0", "id": 3, "method": "tools/call", "params": {
            "name": call["tool"], "arguments": call.get("arguments", {}),
        }})
        result = child.response(3)
        if result.get("isError") or not result.get("content"):
            raise Verdict("FAIL", "mcp-tool-call-failed")
    return len(names)


def command_for(row, artifact, inventory):
    kind = row.get("kind")
    if kind == "suite":
        mode = row.get("mode")
        if mode not in ("interpreter", "native"):
            raise Verdict("FAIL", "suite-mode-invalid")
        return [artifact["path"], "test"] + [item["path"] for item in inventory] + [
            "--mode=" + mode,
            "--no-session-daemon",
            "--sequential",
            "--no-db",
            "--no-cache",
            "--assert-ran",
            "--fail-fast",
        ]
    if kind in ("command", "mcp"):
        args = row.get("args", [])
        if not isinstance(args, list) or any(not isinstance(arg, str) for arg in args):
            raise Verdict("FAIL", "command-args-invalid")
        return [artifact["path"]] + args
    raise Verdict("FAIL", "row-kind-invalid")


def provider_unavailable(row_name, output):
    return row_name in PROVIDER_ROWS and any(
        re.search(pattern, output) for pattern in PROVIDER_UNAVAILABLE_PATTERNS
    )


def process_crashed(code):
    return code < 0 or code >= 128


def check_output(row_name, row, code, output, errors=""):
    if code != 0:
        combined = output + "\n" + errors
        if process_crashed(code):
            raise Verdict("FAIL", "process-crashed")
        if provider_unavailable(row_name, combined):
            raise Verdict("BLOCKED", "provider-auth-or-connectivity-unavailable")
        raise Verdict("FAIL", "process-nonzero-exit")
    lowered = output.lower()
    if any(marker in lowered for marker in (
        "stub fallback", "source fallback", "path-resolved simple", "native_missing",
        "is not the invoking binary",
    )):
        raise Verdict("FAIL", "fallback-or-stale-child-observed")
    if row.get("kind") == "suite":
        match = re.search(r"Results:\s+([1-9][0-9]*) total,\s+([0-9]+) passed,\s+([0-9]+) failed", output)
        if not match or match.group(1) != match.group(2) or match.group(3) != "0":
            raise Verdict("FAIL", "suite-results-marker-invalid")
    for marker in row.get("expected_stdout", []):
        if marker not in output:
            raise Verdict("FAIL", "expected-output-marker-missing")
    if row.get("expected_json") is not None:
        try:
            value = json.loads(output)
        except json.JSONDecodeError:
            raise Verdict("FAIL", "expected-json-output-invalid")
        if any(value.get(key) != expected for key, expected in row["expected_json"].items()):
            raise Verdict("FAIL", "expected-json-value-mismatch")
        if any(not value.get(key) for key in row.get("required_json_fields", [])):
            raise Verdict("FAIL", "expected-json-field-missing")


def row_resume(script, manifest_path, output, timeout, row_name):
    return [
        sys.executable,
        str(script),
        "--manifest", str(manifest_path),
        "--output", str(output.parent / (output.name + "-resume-" + row_name)),
        "--timeout", str(timeout),
        "--row", row_name,
    ]


def run_row(manifest, manifest_path, manifest_sha, output, timeout, row_name, script):
    row = manifest.get("rows", {}).get(row_name)
    receipt = {
        "schema": "BootstrapPhaseFeatureRowV1",
        "phase": manifest["phase"],
        "generation": manifest["generation"],
        "row": row_name,
        "manifest_path": str(manifest_path),
        "manifest_sha256": manifest_sha,
        "selected_bootstrap_jobs": manifest["bootstrap_jobs"]["selected"],
        "detected_cpu_count": manifest["bootstrap_jobs"]["detected_cpu_count"],
        "release_evidence": False,
        "capability_set": manifest["capability_set"],
        "capability_set_sha256": canonical_digest(manifest["capability_set"]),
        "launched": False,
        "resume_argv": row_resume(script, manifest_path, output, timeout, row_name),
    }
    started = time.monotonic()
    child = None
    try:
        current_authority = validate_current_phase_authority(manifest)
        compiler = admitted_artifact(manifest, "compiler")
        receipt.update({
            "compiler_path": compiler["path"],
            "compiler_sha256": compiler["sha256"],
            "compiler_sha256_before": compiler["sha256"],
            "compiler_provenance_path": compiler["provenance_path"],
            "compiler_provenance_sha256": compiler["provenance_sha256"],
            "compiler_admission_path": compiler["admission_path"],
            "compiler_admission_sha256": compiler["admission_sha256"],
        })
        if current_authority:
            receipt.update({
                "current_authority_path": current_authority["path"],
                "current_authority_sha256": current_authority["sha256"],
                "current_authority_sha256_before": current_authority["sha256"],
                "current_seed_stamp_path": current_authority["stamp_path"],
                "current_seed_stamp_sha256": current_authority["stamp_sha256"],
                "current_admitted_compiler_path": current_authority["admitted_compiler_path"],
                "current_admitted_compiler_sha256": current_authority["admitted_compiler_sha256"],
            })
        if row is None:
            raise Verdict("FAIL", "phase-row-not-declared")
        validate_row_shape(row_name, row)
        receipt.update(owner=row["owner"], reviewer=row["reviewer"])
        support = row.get("support")
        if support in ("unsupported", "blocked"):
            reason = row["reason"]
            receipt.update(prerequisite=row["prerequisite"])
            raise Verdict(support.upper(), reason)
        if support != "supported":
            raise Verdict("FAIL", "row-support-state-invalid")
        artifact = admitted_artifact(manifest, row.get("artifact", ""))
        validate_row_pin(row, artifact)
        receipt.update({
            "artifact_name": artifact["name"],
            "executable_path": artifact["path"],
            "executable_sha256": artifact["sha256"],
            "executable_sha256_before": artifact["sha256"],
            "artifact_provenance_path": artifact["provenance_path"],
            "artifact_provenance_sha256": artifact["provenance_sha256"],
            "artifact_admission_path": artifact["admission_path"],
            "artifact_admission_sha256": artifact["admission_sha256"],
        })
        inventory = validate_inventory(row) if row.get("kind") == "suite" else []
        bound_inputs = [
            {"path": bound_file(item), "sha256": item["sha256"]}
            for item in row.get("inputs", [])
        ]
        argv = command_for(row, artifact, inventory)
        if argv[0] != artifact["path"] or not Path(argv[0]).is_absolute():
            raise Verdict("FAIL", "path-resolved-launch-rejected")
        if row_name == "spipe_plugin_launch" and not any(
            item["path"] in argv[1:] for item in bound_inputs
        ):
            raise Verdict("FAIL", "spipe-plugin-entry-not-launched")
        receipt.update({
            "argv": argv,
            "argv_sha256": canonical_digest(argv),
            "inventory": inventory,
            "inventory_sha256": canonical_digest(inventory),
            "inputs": bound_inputs,
            "inputs_sha256": canonical_digest(bound_inputs),
        })
        row_root = output / row_name
        for name in ("home", "tmp", "cache", "outputs"):
            (row_root / name).mkdir(parents=True, exist_ok=False)
        env = dict(os.environ)
        env.update({
            "HOME": str(row_root / "home"),
            "TMPDIR": str(row_root / "tmp"),
            "SIMPLE_CACHE_DIR": str(row_root / "cache"),
            "SIMPLE_NO_STUB_FALLBACK": "1",
            "SIMPLE_MCP_ALLOW_SOURCE_FALLBACK": "0",
            "SIMPLE_BINARY": compiler["path"],
            "SIMPLE_BIN": compiler["path"],
            "NO_COLOR": "1",
        })
        if row.get("credential_home"):
            credential_home = Path(row["credential_home"])
            if not credential_home.is_absolute() or not credential_home.is_dir():
                raise Verdict("BLOCKED", "credential-home-unavailable")
            env["HOME"] = str(credential_home.resolve())
            env["USERPROFILE"] = str(credential_home.resolve())
            env["GH_PROMPT_DISABLED"] = "1"
        child = Child(argv, env, timeout)
        receipt.update(launched=True, pid=child.proc.pid)
        if row.get("kind") == "mcp":
            receipt["mcp_tool_count"] = mcp_probe(child, row)
        code, stdout = child.finish()
        receipt["exit_code"] = code
        errors = child.stderr.decode("utf-8", errors="replace").replace("\r\n", "\n")
        check_output(row_name, row, code, stdout, errors)
        compiler_after = admitted_artifact(manifest, "compiler")
        artifact_after = admitted_artifact(manifest, row["artifact"])
        current_authority_after = validate_current_phase_authority(manifest)
        receipt.update({
            "compiler_sha256_after": compiler_after["sha256"],
            "executable_sha256_after": artifact_after["sha256"],
        })
        if current_authority_after:
            receipt["current_authority_sha256_after"] = current_authority_after["sha256"]
        for item in inventory + bound_inputs:
            bound_file(item)
        if digest(manifest_path) != manifest_sha:
            raise Verdict("FAIL", "manifest-drift")
        receipt.update(status="PASS", reason="exact-phase-artifact-validated")
    except Verdict as error:
        receipt.update(status=error.status, reason=error.reason)
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as error:
        receipt.update(status="FAIL", reason="controller-error:" + type(error).__name__)
    finally:
        if child:
            receipt["stdout_sha256"] = hashlib.sha256(child.stdout).hexdigest()
            receipt["stderr_sha256"] = hashlib.sha256(child.stderr).hexdigest()
            if receipt.get("status") == "FAIL":
                diagnostic = (child.stdout + b"\n" + child.stderr).decode("utf-8", errors="replace")[-4096:]
                diagnostic = re.sub(r"(?i)(token|password|authorization)(\s*[:=]\s*)\S+", r"\1\2<redacted>", diagnostic)
                receipt["diagnostic_excerpt"] = diagnostic
            child.close()
        receipt["duration_ms"] = round((time.monotonic() - started) * 1000)
    return receipt


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", required=True)
    parser.add_argument("--output", required=True)
    parser.add_argument("--timeout", type=int, default=120)
    parser.add_argument("--row", choices=ROWS)
    parser.add_argument("--validate-only", action="store_true")
    args = parser.parse_args(argv)
    if args.timeout < 1 or args.timeout > 1800:
        parser.error("timeout must be 1..1800 seconds")
    manifest_path = Path(args.manifest).resolve()
    try:
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        validate_manifest(manifest)
    except (OSError, UnicodeError, json.JSONDecodeError, Verdict) as error:
        reason = error.reason if isinstance(error, Verdict) else type(error).__name__
        print("matrix=FAIL:" + reason)
        return 1
    if args.validate_only:
        try:
            validate_current_phase_authority(manifest)
            admitted_artifact(manifest, "compiler")
            missing = [name for name in ROWS if name not in manifest.get("rows", {})]
            if missing:
                raise Verdict("FAIL", "required-row-missing:" + missing[0])
            for name, row in manifest.get("rows", {}).items():
                if name not in ROWS:
                    raise Verdict("FAIL", "unknown-row:" + name)
                validate_row_shape(name, row)
                if row.get("support") == "supported":
                    artifact = admitted_artifact(manifest, row.get("artifact", ""))
                    validate_row_pin(row, artifact)
                    if row.get("kind") == "suite":
                        validate_inventory(row)
            print("matrix=PASS:manifest-and-artifact-bindings-valid")
            return 0
        except Verdict as error:
            print("matrix=" + error.status + ":" + error.reason)
            return 1 if error.status == "FAIL" else 2
    output = Path(args.output).resolve()
    output.mkdir(parents=True, exist_ok=True)
    if (output / "summary.json").exists():
        parser.error("summary exists; use a new output directory")
    script = Path(__file__).resolve()
    manifest_sha = digest(manifest_path)
    results = []
    selected_rows = (args.row,) if args.row else ROWS
    for row_name in selected_rows:
        destination = output / (row_name + ".json")
        if destination.exists():
            parser.error("receipt exists; use a new output directory")
        receipt = run_row(manifest, manifest_path, manifest_sha, output, args.timeout, row_name, script)
        destination.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
        results.append(receipt["status"])
        print(row_name + "=" + receipt["status"] + ":" + receipt["reason"])
    summary = {
        "schema": "BootstrapPhaseFeatureMatrixV1",
        "phase": manifest["phase"],
        "generation": manifest["generation"],
        "manifest_sha256": manifest_sha,
        "selected_bootstrap_jobs": manifest["bootstrap_jobs"]["selected"],
        "detected_cpu_count": manifest["bootstrap_jobs"]["detected_cpu_count"],
        "required_rows": list(selected_rows),
        "counts": {status: results.count(status) for status in ("PASS", "FAIL", "BLOCKED", "UNSUPPORTED")},
        "release_evidence": False,
        "capability_set": manifest["capability_set"],
        "capability_set_sha256": canonical_digest(manifest["capability_set"]),
    }
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    return 1 if "FAIL" in results else (2 if any(result != "PASS" for result in results) else 0)


if __name__ == "__main__":
    sys.exit(main())
