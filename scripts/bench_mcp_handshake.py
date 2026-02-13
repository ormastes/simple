#!/usr/bin/env python3
"""Measure MCP initialize latency for the three servers.

Usage: python scripts/bench_mcp_handshake.py [--timeout 2.0]
Prints ms and whether a response was received.
"""
import argparse, json, subprocess, time, select

SERVERS = {
    "simple-mcp": ["bin/simple_mcp_server"],
    "fileio": ["bin/simple_mcp_fileio"],
    "mcp-jj": ["bin/simple", "src/app/mcp_jj/main.spl", "server"],
}

REQ_INIT = {"jsonrpc":"2.0","id":"1","method":"initialize","params":{"protocolVersion":"2025-06-18"}}
REQ_SHUT = {"jsonrpc":"2.0","id":"2","method":"shutdown"}
REQ_EXIT = {"jsonrpc":"2.0","method":"exit"}

def send(p, obj):
    body = json.dumps(obj)
    header = f"Content-Length: {len(body)}\r\n\r\n".encode()
    p.stdin.write(header + body.encode())
    p.stdin.flush()

def measure(cmd, timeout):
    start = time.perf_counter()
    p = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    send(p, REQ_INIT)
    body = None
    ready, _, _ = select.select([p.stdout], [], [], timeout)
    if ready:
        header = p.stdout.readline()
        if header.startswith(b"Content-Length:"):
            length = int(header.decode().split(":",1)[1].strip())
            p.stdout.readline()
            body = p.stdout.read(length)
    elapsed_ms = (time.perf_counter() - start)*1000
    # graceful exit
    try:
        send(p, REQ_SHUT)
        send(p, REQ_EXIT)
        p.wait(timeout=0.5)
    except Exception:
        p.kill()
    return elapsed_ms, body is not None

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--timeout", type=float, default=2.0)
    args = parser.parse_args()
    for name, cmd in SERVERS.items():
        elapsed, ok = measure(cmd, args.timeout)
        print(f"{name}: {elapsed:.1f} ms, response={'yes' if ok else 'no'}")

if __name__ == "__main__":
    main()
