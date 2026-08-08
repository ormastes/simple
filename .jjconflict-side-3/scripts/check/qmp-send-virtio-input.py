#!/usr/bin/env python3
import json
import socket
import sys


def receive(sock):
    data = b""
    while b"\n" not in data:
        chunk = sock.recv(4096)
        if not chunk:
            raise RuntimeError("QMP connection closed")
        data += chunk
    return json.loads(data.split(b"\n", 1)[0])


def execute(sock, command, arguments=None):
    payload = {"execute": command}
    if arguments is not None:
        payload["arguments"] = arguments
    sock.sendall(json.dumps(payload).encode() + b"\n")
    while True:
        response = receive(sock)
        if "return" in response:
            return
        if "error" in response:
            raise RuntimeError(response["error"])


def main():
    if len(sys.argv) != 2:
        raise SystemExit("usage: qmp-send-virtio-input.py SOCKET")
    with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as sock:
        sock.connect(sys.argv[1])
        receive(sock)
        execute(sock, "qmp_capabilities")
        execute(sock, "input-send-event", {"events": [
            {"type": "key", "data": {"down": True, "key": {"type": "qcode", "data": "a"}}},
            {"type": "key", "data": {"down": False, "key": {"type": "qcode", "data": "a"}}},
            {"type": "rel", "data": {"axis": "x", "value": 7}},
            {"type": "rel", "data": {"axis": "y", "value": 5}},
            {"type": "btn", "data": {"down": True, "button": "left"}},
            {"type": "btn", "data": {"down": False, "button": "left"}},
        ]})


if __name__ == "__main__":
    main()
