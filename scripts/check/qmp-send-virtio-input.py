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


def validate_ppm_capture(path, expected_width, expected_height):
    with open(path, "rb") as capture:
        data = capture.read()
    # QEMU screendump emits binary P6. Exact geometry/payload rejects empty or
    # stale files before they can be promoted as visual evidence.
    parts = data.split(None, 4)
    if len(parts) != 5 or parts[0] != b"P6":
        raise RuntimeError("capture is not a binary PPM")
    width = int(parts[1])
    height = int(parts[2])
    maximum = int(parts[3])
    pixels = parts[4]
    if (width, height, maximum) != (expected_width, expected_height, 255):
        raise RuntimeError("capture geometry or channel depth mismatch")
    if len(pixels) != width * height * 3:
        raise RuntimeError("capture pixel payload is incomplete")
    first_pixel = pixels[:3]
    if not any(pixels[offset:offset + 3] != first_pixel for offset in range(3, len(pixels), 3)):
        raise RuntimeError("capture is a uniform surface")


def main():
    if len(sys.argv) not in (2, 6):
        raise SystemExit("usage: qmp-send-virtio-input.py SOCKET [--capture-only CAPTURE.ppm WIDTH HEIGHT]")
    with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as sock:
        sock.connect(sys.argv[1])
        receive(sock)
        execute(sock, "qmp_capabilities")
        if len(sys.argv) == 6:
            if sys.argv[2] != "--capture-only":
                raise RuntimeError("unknown mode")
            execute(sock, "screendump", {"filename": sys.argv[3]})
            validate_ppm_capture(sys.argv[3], int(sys.argv[4]), int(sys.argv[5]))
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
            # interaction-driven device frames for a 20-sample distribution.
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
