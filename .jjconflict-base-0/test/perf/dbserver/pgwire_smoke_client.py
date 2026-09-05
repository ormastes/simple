#!/usr/bin/env python3
"""Small PostgreSQL v3 startup/simple-query interoperability probe."""

from __future__ import annotations

import argparse
import socket
import struct


def startup(user: str, database: str) -> bytes:
    payload = struct.pack("!I", 196608)
    payload += b"user\0" + user.encode() + b"\0"
    payload += b"database\0" + database.encode() + b"\0\0"
    return struct.pack("!I", len(payload) + 4) + payload


def message(kind: bytes, payload: bytes) -> bytes:
    return kind + struct.pack("!I", len(payload) + 4) + payload


def receive_until_ready(sock: socket.socket) -> list[tuple[str, bytes]]:
    received: list[tuple[str, bytes]] = []
    while True:
        kind = sock.recv(1)
        if not kind:
            raise RuntimeError("peer closed before ReadyForQuery")
        length_raw = recv_exact(sock, 4)
        length = struct.unpack("!I", length_raw)[0]
        if length < 4 or length > 16 * 1024 * 1024:
            raise RuntimeError(f"invalid backend frame length: {length}")
        payload = recv_exact(sock, length - 4)
        received.append((kind.decode("ascii", "replace"), payload))
        if kind == b"E":
            raise RuntimeError(f"server ErrorResponse: {payload!r}")
        if kind == b"Z":
            return received


def recv_exact(sock: socket.socket, count: int) -> bytes:
    chunks = bytearray()
    while len(chunks) < count:
        chunk = sock.recv(count - len(chunks))
        if not chunk:
            raise RuntimeError("peer closed in backend frame")
        chunks.extend(chunk)
    return bytes(chunks)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--host", default="127.0.0.1")
    parser.add_argument("--port", type=int, required=True)
    parser.add_argument("--user", required=True)
    parser.add_argument("--database", required=True)
    parser.add_argument("--query", action="append", default=[])
    args = parser.parse_args()
    if not (1 <= args.port <= 65535) or not args.query:
        parser.error("valid --port and at least one --query are required")

    with socket.create_connection((args.host, args.port), timeout=5) as sock:
        sock.settimeout(5)
        sock.sendall(startup(args.user, args.database))
        startup_frames = receive_until_ready(sock)
        if not any(kind == "R" and payload == b"\0\0\0\0" for kind, payload in startup_frames):
            raise RuntimeError("AuthenticationOk was not observed")
        print("startup=" + ",".join(kind for kind, _ in startup_frames))
        for query in args.query:
            sock.sendall(message(b"Q", query.encode() + b"\0"))
            frames = receive_until_ready(sock)
            print("query=" + query)
            print("frames=" + ",".join(kind for kind, _ in frames))
            for kind, payload in frames:
                if kind == "D":
                    print("data_row_hex=" + payload.hex())
        sock.sendall(message(b"X", b""))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
