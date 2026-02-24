#!/usr/bin/env python3
import json
import subprocess
import sys
from typing import Any


def send_msg(stdin, obj: dict[str, Any]) -> None:
    body = json.dumps(obj, separators=(",", ":")).encode("utf-8")
    header = f"Content-Length: {len(body)}\r\n\r\n".encode("ascii")
    stdin.write(header)
    stdin.write(body)
    stdin.flush()


def read_msg(stdout) -> dict[str, Any]:
    line = stdout.readline()
    if not line:
        raise RuntimeError("EOF while reading MCP header")
    headers = [line]
    while True:
        line = stdout.readline()
        if not line:
            raise RuntimeError("EOF before MCP body")
        if line in (b"\r\n", b"\n"):
            break
        headers.append(line)
    content_length = None
    for raw in headers:
        k, _, v = raw.partition(b":")
        if k.strip().lower() == b"content-length":
            content_length = int(v.strip())
            break
    if content_length is None:
        raise RuntimeError("Missing Content-Length")
    body = stdout.read(content_length)
    if len(body) != content_length:
        raise RuntimeError("Short read on MCP body")
    return json.loads(body.decode("utf-8"))


def tool_call(proc, msg_id: int, name: str, arguments: dict[str, Any]) -> dict[str, Any]:
    send_msg(
        proc.stdin,
        {
            "jsonrpc": "2.0",
            "id": str(msg_id),
            "method": "tools/call",
            "params": {"name": name, "arguments": arguments},
        },
    )
    return read_msg(proc.stdout)


def assert_ok(cond: bool, msg: str) -> None:
    if not cond:
        raise RuntimeError(msg)


def main() -> int:
    proc = subprocess.Popen(
        ["bin/simple_mcp_server"],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
    )
    assert proc.stdin is not None
    assert proc.stdout is not None
    try:
        send_msg(
            proc.stdin,
            {
                "jsonrpc": "2.0",
                "id": "1",
                "method": "initialize",
                "params": {
                    "protocolVersion": "2025-06-18",
                    "capabilities": {},
                    "clientInfo": {"name": "probe-python", "version": "1.0"},
                },
            },
        )
        init_resp = read_msg(proc.stdout)
        assert_ok("result" in init_resp, "initialize failed")

        send_msg(proc.stdin, {"jsonrpc": "2.0", "method": "initialized", "params": {}})

        send_msg(proc.stdin, {"jsonrpc": "2.0", "id": "2", "method": "tools/list", "params": {}})
        tools_resp = read_msg(proc.stdout)
        tools = tools_resp.get("result", {}).get("tools", [])
        names = {t.get("name", "") for t in tools}
        assert_ok("debug_create_session" in names, "debug_create_session missing from tools/list")
        assert_ok("debug_log_status" in names, "debug_log_status missing from tools/list")

        create_resp = tool_call(proc, 3, "debug_create_session", {"program": "src/app/mcp/main.spl"})
        create_text = create_resp["result"]["content"][0]["text"]
        create_data = json.loads(create_text)
        session_id = create_data.get("session_id", "")
        assert_ok(session_id != "", "debug_create_session did not return session_id")

        list_resp = tool_call(proc, 4, "debug_list_sessions", {})
        list_text = list_resp["result"]["content"][0]["text"]
        assert_ok(session_id in list_text, "debug_list_sessions did not include created session")

        enable_resp = tool_call(proc, 5, "debug_log_enable", {"pattern": "*"})
        enable_text = enable_resp["result"]["content"][0]["text"]
        assert_ok("enabled" in enable_text, "debug_log_enable did not enable logging")

        status_resp = tool_call(proc, 6, "debug_log_status", {})
        status_text = status_resp["result"]["content"][0]["text"]
        assert_ok("\"enabled\":true" in status_text, "debug_log_status did not report enabled=true")

        print(f"python probe: OK (session={session_id})")

        send_msg(proc.stdin, {"jsonrpc": "2.0", "id": "7", "method": "shutdown", "params": {}})
        _ = read_msg(proc.stdout)
        return 0
    finally:
        try:
            proc.terminate()
        except Exception:
            pass
        proc.wait(timeout=2)


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(f"python probe: FAIL - {exc}", file=sys.stderr)
        raise
