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
    if len(sys.argv) not in (2, 4):
        raise SystemExit("usage: qmp-send-virtio-input.py SOCKET [--capture-only CAPTURE.ppm]")
    with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as sock:
        sock.connect(sys.argv[1])
        receive(sock)
        execute(sock, "qmp_capabilities")
        if len(sys.argv) == 4:
            if sys.argv[2] != "--capture-only":
                raise RuntimeError("unknown mode")
            execute(sock, "screendump", {"filename": sys.argv[3]})
            return
        execute(sock, "input-send-event", {"events": [
            {"type": "rel", "data": {"axis": "x", "value": 7}},
            {"type": "rel", "data": {"axis": "y", "value": 5}},
            {"type": "btn", "data": {"down": True, "button": "left"}},
            {"type": "rel", "data": {"axis": "x", "value": 11}},
            {"type": "rel", "data": {"axis": "y", "value": 3}},
            {"type": "btn", "data": {"down": False, "button": "left"}},
            {"type": "btn", "data": {"down": True, "button": "wheel-up"}},
            {"type": "btn", "data": {"down": False, "button": "wheel-up"}},
            {"type": "key", "data": {"down": True, "key": {"type": "qcode", "data": "ctrl"}}},
            {"type": "key", "data": {"down": False, "key": {"type": "qcode", "data": "ctrl"}}},
            {"type": "key", "data": {"down": True, "key": {"type": "qcode", "data": "ctrl_r"}}},
            {"type": "key", "data": {"down": False, "key": {"type": "qcode", "data": "ctrl_r"}}},
            {"type": "key", "data": {"down": True, "key": {"type": "qcode", "data": "alt"}}},
            {"type": "key", "data": {"down": False, "key": {"type": "qcode", "data": "alt"}}},
            {"type": "key", "data": {"down": True, "key": {"type": "qcode", "data": "alt_r"}}},
            {"type": "key", "data": {"down": False, "key": {"type": "qcode", "data": "alt_r"}}},
            # Seven real focus transitions (press + release) provide enough
            # changed device frames for a 20-sample performance distribution.
            # They are deliberately sent only after the frozen primitive
            # sequence above, so they cannot manufacture its admission.
            {"type": "key", "data": {"down": True, "key": {"type": "qcode", "data": "tab"}}},
            {"type": "key", "data": {"down": False, "key": {"type": "qcode", "data": "tab"}}},
            {"type": "key", "data": {"down": True, "key": {"type": "qcode", "data": "tab"}}},
            {"type": "key", "data": {"down": False, "key": {"type": "qcode", "data": "tab"}}},
            {"type": "key", "data": {"down": True, "key": {"type": "qcode", "data": "tab"}}},
            {"type": "key", "data": {"down": False, "key": {"type": "qcode", "data": "tab"}}},
            {"type": "key", "data": {"down": True, "key": {"type": "qcode", "data": "tab"}}},
            {"type": "key", "data": {"down": False, "key": {"type": "qcode", "data": "tab"}}},
            {"type": "key", "data": {"down": True, "key": {"type": "qcode", "data": "tab"}}},
            {"type": "key", "data": {"down": False, "key": {"type": "qcode", "data": "tab"}}},
            {"type": "key", "data": {"down": True, "key": {"type": "qcode", "data": "tab"}}},
            {"type": "key", "data": {"down": False, "key": {"type": "qcode", "data": "tab"}}},
            {"type": "key", "data": {"down": True, "key": {"type": "qcode", "data": "tab"}}},
            {"type": "key", "data": {"down": False, "key": {"type": "qcode", "data": "tab"}}},
        ]})


if __name__ == "__main__":
    main()
