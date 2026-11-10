#!/usr/bin/env python3
"""Exercise the real timing gate with controlled MCP subprocess responses."""
import argparse
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


EMITTER = r'''
import json, os, sys
mode = os.environ["MCP_PERF_CASE_" + sys.argv[1].upper()]
sys.stdin.buffer.read()
init = {"jsonrpc": "2.0", "id": "1", "result": {
    "protocolVersion": "2025-06-18", "capabilities": {},
    "serverInfo": {"name": "fixture", "version": "1"}}}
tools = {"jsonrpc": "2.0", "id": "2", "result": {"tools": []}}
notification = {"jsonrpc": "2.0", "method": "notifications/tools/list_changed"}
messages = [init, tools]
if mode == "empty": messages = []
elif mode == "missing": messages = [init]
elif mode == "foreign": tools["id"] = "other"
elif mode == "duplicate": messages.append(tools)
elif mode == "error": tools = {"jsonrpc": "2.0", "id": "2", "error": {"code": -32603, "message": "failure"}}; messages = [init, tools]
elif mode == "invalid_init": init["result"] = {}
elif mode == "invalid_tools": tools["result"]["tools"] = {}
elif mode == "invalid_tool": tools["result"]["tools"] = [{"name": "missing-schema"}]
elif mode == "numeric_id": tools["id"] = 2
elif mode == "nonfinite": init["result"]["capabilities"]["invalid"] = float("nan")
elif mode in ("unicode", "wrong_length"):
    init["result"]["serverInfo"]["name"] = "한글"
    messages = [tools, notification, init]
data = b""
for message in messages:
    body = json.dumps(message, ensure_ascii=False).encode("utf-8")
    if mode == "duplicate_member": body = body.replace(b'"id": "2"', b'"id": "wrong", "id": "2"')
    length = len(body.decode("utf-8")) if mode == "wrong_length" else len(body)
    data += ("Content-Length: %d\r\n\r\n" % length).encode() + body
if mode == "truncated": data = data[:-1]
elif mode == "trailing": data += b"not a frame"
sys.stdout.buffer.write(data)
sys.exit(7 if mode == "nonzero" else 0)
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("build/test-artifacts/mcp-script-mode-perf-contract"))
    parser.add_argument("--case", action="append", help="Run only these named controls after a focused repair")
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    shell = shutil.which("sh")
    if not shell:
        parser.error("POSIX sh is required (Git sh on Windows)")
    gate = Path(__file__).resolve().with_name("check-mcp-script-mode-perf.shs")
    cases = [("valid", "valid", True), ("unicode", "valid", True)]
    cases += [(name, "valid", False) for name in (
        "empty", "missing", "foreign", "duplicate", "error", "invalid_init",
        "invalid_tools", "invalid_tool", "numeric_id", "wrong_length", "truncated",
        "trailing", "duplicate_member", "nonfinite", "nonzero")]
    cases += [("valid", "empty", False)]
    if args.case:
        names = {mcp + "_" + lsp for mcp, lsp, _ in cases}
        if set(args.case) - names:
            parser.error("unknown control name")
        cases = [case for case in cases if case[0] + "_" + case[1] in args.case]
    failures = 0
    records = ["cases |name, expected_success, exit_code, passed|"]
    with tempfile.TemporaryDirectory(prefix="mcp-perf-contract-") as directory:
        root = Path(directory)
        (root / "bin").mkdir()
        emitter = root / "emit.py"
        emitter.write_text(EMITTER, encoding="utf-8")
        for kind, name in (("mcp", "simple_mcp_server"), ("lsp", "simple_lsp_mcp_server")):
            wrapper = root / "bin" / name
            wrapper.write_text('#!/bin/sh\nexec "$MCP_PERF_FIXTURE_PYTHON" "$MCP_PERF_FIXTURE_EMITTER" ' + kind + '\n', encoding="utf-8", newline="\n")
            wrapper.chmod(0o755)
        for mcp_case, lsp_case, expected in cases:
            name = mcp_case + "_" + lsp_case
            environment = os.environ.copy()
            environment.update(RUNS="1", MCP_SCRIPT_PERF_STRICT="0", MCP_SCRIPT_PERF_USE_SMF="0",
                               MCP_PERF_FIXTURE_PYTHON=sys.executable, MCP_PERF_FIXTURE_EMITTER=str(emitter),
                               MCP_PERF_CASE_MCP=mcp_case, MCP_PERF_CASE_LSP=lsp_case)
            completed = subprocess.run([shell, str(gate)], cwd=root, env=environment,
                                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                       text=True, encoding="utf-8", timeout=45)
            (args.output / (name + ".log")).write_text(completed.stdout, encoding="utf-8")
            passed = (completed.returncode == 0) == expected
            if expected:
                passed = passed and "simple_lsp_mcp_script_median_ms=" in completed.stdout
            else:
                passed = passed and ("protocol_validation_failed" in completed.stdout or
                                     "command_failed_rc=7" in completed.stdout)
                passed = passed and "mcp_script_perf_status=pass" not in completed.stdout
                if mcp_case == "duplicate_member":
                    passed = passed and "invalid_mcp_response=duplicate JSON member" in completed.stdout
                if mcp_case == "nonfinite":
                    passed = passed and "invalid_mcp_response=nonfinite JSON constant" in completed.stdout
            failures += not passed
            records.append(f"    {name}, {str(expected).lower()}, {completed.returncode}, {str(passed).lower()}")
            print(("PASS " if passed else "FAIL ") + name, flush=True)
    (args.output / "results.sdn").write_text("\n".join(records) + "\n", encoding="utf-8")
    print(f"mcp_perf_contract_cases={len(cases)} failures={failures}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
