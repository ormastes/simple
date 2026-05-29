#!/usr/bin/env python3
"""Live protocol smoke for `bin/simple lsp`."""

import json
import os
import select
import subprocess
import sys
import time


ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))


def _frame(message):
    payload = json.dumps(message, separators=(",", ":")).encode("utf-8")
    return b"Content-Length: " + str(len(payload)).encode("ascii") + b"\r\n\r\n" + payload


def _send(proc, message):
    proc.stdin.write(_frame(message))
    proc.stdin.flush()


def _recv(proc, timeout=5.0):
    deadline = time.time() + timeout
    buf = b""
    fd = proc.stdout.fileno()
    while time.time() < deadline:
        ready, _, _ = select.select([fd], [], [], 0.1)
        if not ready:
            continue
        chunk = os.read(fd, 4096)
        if not chunk:
            break
        buf += chunk
        header_end = buf.find(b"\r\n\r\n")
        if header_end < 0:
            continue
        header = buf[:header_end].decode("ascii", errors="replace")
        content_start = header_end + 4
        content_length = 0
        for line in header.split("\r\n"):
            if line.lower().startswith("content-length:"):
                content_length = int(line.split(":", 1)[1].strip())
        if content_length > 0 and len(buf) >= content_start + content_length:
            payload = buf[content_start : content_start + content_length]
            return json.loads(payload.decode("utf-8"))
    raise TimeoutError("timed out waiting for LSP response")


def _request(proc, request_id, method, params):
    _send(proc, {"jsonrpc": "2.0", "id": request_id, "method": method, "params": params})
    response = _recv(proc)
    if "error" in response:
        raise AssertionError(f"{method} returned error: {response['error']}")
    if "result" not in response:
        raise AssertionError(f"{method} response missing result: {response}")
    return response["result"]


def main():
    proc = subprocess.Popen(
        ["bin/simple", "lsp"],
        cwd=ROOT,
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    try:
        init = _request(
            proc,
            1,
            "initialize",
            {
                "processId": None,
                "rootUri": "file://" + ROOT,
                "capabilities": {},
            },
        )
        capabilities = init.get("capabilities", {})
        for key in ("completionProvider", "definitionProvider", "codeActionProvider"):
            if key not in capabilities:
                raise AssertionError(f"initialize capabilities missing {key}")

        _send(proc, {"jsonrpc": "2.0", "method": "initialized", "params": {}})
        uri = "file:///tmp/simple_lsp_protocol_smoke.spl"
        source = "fn main():\n    pri\n"
        _send(
            proc,
            {
                "jsonrpc": "2.0",
                "method": "textDocument/didOpen",
                "params": {
                    "textDocument": {
                        "uri": uri,
                        "languageId": "simple",
                        "version": 1,
                        "text": source,
                    }
                },
            },
        )

        completion = _request(
            proc,
            2,
            "textDocument/completion",
            {"textDocument": {"uri": uri}, "position": {"line": 1, "character": 7}},
        )
        if not isinstance(completion, list):
            raise AssertionError("completion result must be a list")

        definition = _request(
            proc,
            3,
            "textDocument/definition",
            {"textDocument": {"uri": uri}, "position": {"line": 0, "character": 3}},
        )
        if definition is not None and not isinstance(definition, (dict, list)):
            raise AssertionError("definition result must be null, object, or list")

        actions = _request(
            proc,
            4,
            "textDocument/codeAction",
            {
                "textDocument": {"uri": uri},
                "range": {
                    "start": {"line": 1, "character": 4},
                    "end": {"line": 1, "character": 7},
                },
                "context": {"diagnostics": [], "only": ["quickfix"]},
            },
        )
        if not isinstance(actions, list):
            raise AssertionError("codeAction result must be a list")

        _request(proc, 5, "shutdown", {})
        _send(proc, {"jsonrpc": "2.0", "method": "exit"})
        print("STATUS: PASS simple_lsp_protocol_smoke")
        return 0
    finally:
        try:
            proc.terminate()
            proc.wait(timeout=2)
        except Exception:
            proc.kill()


if __name__ == "__main__":
    sys.exit(main())
