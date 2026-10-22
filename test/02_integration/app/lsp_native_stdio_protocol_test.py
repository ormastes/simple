#!/usr/bin/env python3
"""Exercise an explicit native LSP MCP binary with stdin held open.

Usage: python lsp_native_stdio_protocol_test.py --binary /absolute/server --receipt out.json
No source runner, build, seed lookup, or binary fallback is performed.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path
import queue
import subprocess
import threading
import time

MAX_STREAM_BYTES = 4 * 1024 * 1024
REQUESTS = [
    {"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {
        "protocolVersion": "2024-11-05", "capabilities": {},
        "clientInfo": {"name": "bootstrap-sanity", "version": "1"}}},
    {"jsonrpc": "2.0", "id": 2, "method": "tools/list", "params": {}},
]


def digest(path):
    result = hashlib.sha256()
    with path.open("rb") as stream:
        for part in iter(lambda: stream.read(1024 * 1024), b""):
            result.update(part)
    return result.hexdigest()


def drain(stream, chunks, failures, label):
    """Blocking pipe reads run in threads, including on Windows."""
    total = 0
    try:
        while True:
            chunk = stream.read(65536)
            if not chunk:
                break
            total += len(chunk)
            if total > MAX_STREAM_BYTES:
                failures.append(label + " exceeded output limit")
                break
            chunks.put(chunk)
    except Exception as error:
        failures.append(label + ": " + str(error))
    finally:
        chunks.put(None)


def extract(buffer, mode):
    if mode == "jsonl":
        if b"\n" not in buffer:
            return None
        return tuple(buffer.split(b"\n", 1))
    if b"\r\n\r\n" not in buffer:
        return None
    header, payload = buffer.split(b"\r\n\r\n", 1)
    lengths = []
    for line in header.split(b"\r\n"):
        key, separator, value = line.partition(b":")
        if not separator:
            raise ValueError("malformed frame header")
        if key.strip().lower() == b"content-length":
            value = value.strip()
            if not value or not value.isdigit():
                raise ValueError("invalid Content-Length")
            lengths.append(int(value))
    if len(lengths) != 1 or lengths[0] > MAX_STREAM_BYTES:
        raise ValueError("missing, duplicate, or excessive Content-Length")
    size = lengths[0]
    if len(payload) < size:
        return None
    return payload[:size], payload[size:]


def run_mode(binary, mode, timeout, tool_validator=None):
    start = time.monotonic()
    result = {"mode": mode, "pass": False, "response_count": 0,
              "stdin_open_during_responses": False, "failure": None}
    process = None
    threads = []
    output, errors = queue.Queue(), queue.Queue()
    failures = []
    buffer = b""
    try:
        process = subprocess.Popen([str(binary)], stdin=subprocess.PIPE,
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                   bufsize=0)
        for stream, chunks, label in [(process.stdout, output, "stdout"),
                                      (process.stderr, errors, "stderr")]:
            thread = threading.Thread(target=drain, args=(stream, chunks, failures, label),
                                      daemon=True)
            thread.start()
            threads.append(thread)
        for request in REQUESTS:
            body = json.dumps(request, separators=(",", ":")).encode()
            wire = body + b"\n" if mode == "jsonl" else (
                b"Content-Length: " + str(len(body)).encode() + b"\r\n\r\n" + body)
            # Requests are small; handle partial writes explicitly on unbuffered pipes.
            remaining = memoryview(wire)
            while remaining:
                written = process.stdin.write(remaining)
                if not written:
                    raise RuntimeError("stdin closed during request")
                remaining = remaining[written:]
            process.stdin.flush()
            deadline = time.monotonic() + timeout
            frame = extract(buffer, mode)
            while frame is None:
                left = deadline - time.monotonic()
                if left <= 0:
                    raise TimeoutError("response unavailable while stdin open")
                try:
                    chunk = output.get(timeout=left)
                except queue.Empty:
                    raise TimeoutError("response unavailable while stdin open") from None
                if chunk is None:
                    raise RuntimeError("server stdout closed before response")
                buffer += chunk
                frame = extract(buffer, mode)
            raw, buffer = frame
            reply = json.loads(raw)
            if (reply.get("jsonrpc") != "2.0" or reply.get("id") != request["id"]
                    or "result" not in reply or "error" in reply):
                raise ValueError("invalid JSON-RPC response")
            if request["method"] == "initialize":
                if not reply["result"]["serverInfo"]["name"]:
                    raise ValueError("missing server name")
            else:
                tools = reply["result"]["tools"]
                if not tools:
                    raise ValueError("empty tools/list")
                if tool_validator is not None:
                    tool_validator(tools)
                result["tool_count"] = len(tools)
            result["response_count"] += 1
        result["stdin_open_during_responses"] = not process.stdin.closed
    except Exception as error:
        result["failure"] = type(error).__name__ + ": " + str(error)
    finally:
        if process is not None:
            try:
                process.stdin.close()
            except OSError:
                pass
            try:
                process.wait(timeout=2)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait(timeout=2)
                failures.append("server did not exit after stdin closed")
            for thread in threads:
                thread.join(timeout=2)
                if thread.is_alive():
                    failures.append("pipe reader did not terminate")
            stderr = b""
            while not errors.empty():
                chunk = errors.get_nowait()
                if chunk is not None:
                    stderr += chunk
            while not output.empty():
                chunk = output.get_nowait()
                if chunk is not None:
                    buffer += chunk
            result.update(exit=process.returncode, stderr=stderr.decode(errors="replace"))
            if stderr:
                failures.append("nonempty stderr")
            if buffer:
                failures.append("unexpected trailing stdout")
            result["pass"] = (result["failure"] is None and not failures
                              and process.returncode == 0 and result["response_count"] == 2
                              and result["stdin_open_during_responses"])
            for stream in [process.stdout, process.stderr]:
                stream.close()
        result["pipe_failures"] = failures
        result["seconds"] = time.monotonic() - start
    return result


def main(tool_validator=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", required=True, type=Path)
    parser.add_argument("--receipt", required=True, type=Path)
    parser.add_argument("--timeout", type=float, default=5.0)
    args = parser.parse_args()
    if not args.binary.is_absolute() or not args.binary.is_file():
        parser.error("--binary must name an existing absolute native binary")
    if not math.isfinite(args.timeout) or not 0 < args.timeout <= 60:
        parser.error("--timeout must be finite and in (0, 60]")
    binary = args.binary.resolve(strict=True)
    if args.receipt.resolve() == binary:
        parser.error("receipt must not overwrite the tested binary")
    before = digest(binary)
    results = [run_mode(binary, mode, args.timeout, tool_validator) for mode in ("jsonl", "content-length")]
    after = digest(binary)
    passed = before == after and all(item["pass"] for item in results)
    receipt = {"binary": str(binary), "sha256_before": before, "sha256_after": after,
               "pass": passed, "results": results}
    args.receipt.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(receipt))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
