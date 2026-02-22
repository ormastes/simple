#!/usr/bin/env python3
"""
MCP stdio framing proxy.

Bridges between strict Content-Length clients and MCP servers that read
JSON lines from stdin.
"""

import os
import subprocess
import sys
import threading
import time


def read_message(stream, framing_cb=None):
    line = stream.readline()
    if not line:
        return None

    # JSON-lines framing
    if line.startswith(b"{"):
        if framing_cb is not None:
            framing_cb("json-lines")
        return line.rstrip(b"\r\n")

    # Content-Length framing
    headers = [line]
    while True:
        line = stream.readline()
        if not line:
            return None
        if line in (b"\r\n", b"\n"):
            break
        headers.append(line)

    content_length = None
    for header in headers:
        if b":" not in header:
            continue
        key, value = header.split(b":", 1)
        if key.strip().lower() == b"content-length":
            try:
                content_length = int(value.strip())
            except ValueError:
                return None

    if framing_cb is not None:
        framing_cb("content-length")

    if content_length is None or content_length < 0:
        return None

    body = stream.read(content_length)
    if body is None or len(body) < content_length:
        return None
    return body


def write_content_length(stream, body):
    header = f"Content-Length: {len(body)}\r\n\r\n".encode("ascii")
    stream.write(header)
    stream.write(body)
    stream.flush()


def write_json_line(stream, body):
    stream.write(body + b"\n")
    stream.flush()


def client_to_server(client_in, server_in, set_framing):
    try:
        while True:
            msg = read_message(client_in, framing_cb=set_framing)
            if msg is None:
                break
            server_in.write(msg + b"\n")
            server_in.flush()
    except BrokenPipeError:
        pass
    finally:
        try:
            server_in.close()
        except Exception:
            pass


def server_to_client(server_out, client_out, get_framing):
    try:
        while True:
            msg = read_message(server_out)
            if msg is None:
                break
            framing = get_framing()
            if framing == "json-lines":
                write_json_line(client_out, msg)
            else:
                write_content_length(client_out, msg)
    except BrokenPipeError:
        pass
    finally:
        try:
            client_out.flush()
        except Exception:
            pass


def main():
    if len(sys.argv) < 2:
        print("usage: mcp_stdio_proxy.py <server-cmd> [args...]", file=sys.stderr)
        return 2

    child = subprocess.Popen(
        sys.argv[1:],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        env=os.environ.copy(),
    )

    framing_state = {"value": None}
    framing_lock = threading.Lock()

    def set_framing(mode):
        with framing_lock:
            if framing_state["value"] is None:
                framing_state["value"] = mode

    def get_framing():
        with framing_lock:
            return framing_state["value"]

    t_client = threading.Thread(
        target=client_to_server,
        args=(sys.stdin.buffer, child.stdin, set_framing),
        daemon=True,
    )
    t_server = threading.Thread(
        target=server_to_client,
        args=(child.stdout, sys.stdout.buffer, get_framing),
        daemon=True,
    )

    t_client.start()
    t_server.start()

    client_closed_at = None
    while True:
        child_exited = child.poll() is not None
        client_alive = t_client.is_alive()
        server_alive = t_server.is_alive()

        # If the output forwarding thread is done, there's nothing left to proxy.
        if not server_alive:
            break

        # Child exited while client is still connected (crash/early exit).
        # Stop so caller can restart/recover.
        if child_exited and client_alive:
            break

        # Keep the proxy alive after stdin closes long enough to flush the
        # server's final response. This fixes one-shot pipeline probes.
        if not client_alive and client_closed_at is None:
            client_closed_at = time.monotonic()

        if child_exited and not client_alive:
            t_server.join(timeout=0.25)
            if not t_server.is_alive():
                break

        # Safety valve: do not wait forever after client EOF.
        if client_closed_at is not None and not child_exited:
            if time.monotonic() - client_closed_at > 2.0:
                break

        time.sleep(0.05)

    if child.poll() is None:
        child.terminate()
        try:
            child.wait(timeout=1.5)
        except subprocess.TimeoutExpired:
            child.kill()
            child.wait(timeout=1.0)
    t_client.join(timeout=0.2)
    t_server.join(timeout=0.2)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
