#!/usr/bin/env python3
"""
Simple Language Jupyter Kernel Wrapper

Thin Python ZMQ bridge that:
1. Reads Jupyter connection file (transport, ip, key, 5 ports)
2. Sets up ZMQ sockets (ROUTER for shell/control, PUB for iopub, REP for heartbeat)
3. Spawns the Simple kernel process (bin/release/simple src/app/jupyter_kernel/main.spl)
4. Bridges ZMQ multipart messages <-> stdin/stdout JSON-lines

The Simple kernel handles all language evaluation logic.
"""

import json
import os
import sys
import hmac
import hashlib
import uuid
import time
import struct
import threading
import subprocess

try:
    import zmq
except ImportError:
    print("Error: pyzmq is required. Install with: pip install pyzmq", file=sys.stderr)
    sys.exit(1)

# Jupyter wire protocol delimiter
DELIMITER = b"<IDS|MSG>"


def read_connection_file(path):
    """Parse Jupyter connection file."""
    with open(path) as f:
        return json.load(f)


def make_url(transport, ip, port):
    """Construct ZMQ URL from connection info."""
    return f"{transport}://{ip}:{port}"


class SimpleKernel:
    """Bridge between Jupyter ZMQ protocol and Simple kernel process."""

    def __init__(self, connection_file):
        self.config = read_connection_file(connection_file)
        self.key = self.config.get("key", "").encode("utf-8")
        self.session_id = str(uuid.uuid4())

        # Find simple binary
        self.simple_bin = self._find_simple_binary()

        # ZMQ context and sockets
        self.ctx = zmq.Context()
        self.shell_socket = self.ctx.socket(zmq.ROUTER)
        self.control_socket = self.ctx.socket(zmq.ROUTER)
        self.iopub_socket = self.ctx.socket(zmq.PUB)
        self.stdin_socket = self.ctx.socket(zmq.ROUTER)
        self.heartbeat_socket = self.ctx.socket(zmq.REP)

        # Bind sockets
        transport = self.config.get("transport", "tcp")
        ip = self.config.get("ip", "127.0.0.1")
        self.shell_socket.bind(make_url(transport, ip, self.config["shell_port"]))
        self.control_socket.bind(make_url(transport, ip, self.config["control_port"]))
        self.iopub_socket.bind(make_url(transport, ip, self.config["iopub_port"]))
        self.stdin_socket.bind(make_url(transport, ip, self.config["stdin_port"]))
        self.heartbeat_socket.bind(make_url(transport, ip, self.config["hb_port"]))

        # Simple kernel process
        self.process = None
        self._response_lock = threading.Lock()
        self._pending_responses = {}

    def _find_simple_binary(self):
        """Find the Simple binary."""
        # Check relative paths from likely locations
        candidates = [
            os.path.join(os.path.dirname(__file__), "..", "..", "bin", "release", "simple"),
            os.path.join(os.getcwd(), "bin", "release", "simple"),
            "bin/release/simple",
        ]
        for c in candidates:
            if os.path.isfile(c) and os.access(c, os.X_OK):
                return os.path.abspath(c)
        # Fallback: assume it's in PATH
        return "simple"

    def sign(self, parts):
        """Compute HMAC-SHA256 signature over message parts."""
        if not self.key:
            return b""
        h = hmac.new(self.key, digestmod=hashlib.sha256)
        for part in parts:
            h.update(part)
        return h.hexdigest().encode("utf-8")

    def send_zmq_message(self, socket, identities, msg_type, content,
                         parent_header=None, metadata=None):
        """Send a Jupyter wire protocol message on a ZMQ socket."""
        header = {
            "msg_id": str(uuid.uuid4()),
            "session": self.session_id,
            "username": "simple_kernel",
            "date": time.strftime("%Y-%m-%dT%H:%M:%S.000000Z", time.gmtime()),
            "msg_type": msg_type,
            "version": "5.4",
        }

        if parent_header is None:
            parent_header = {}
        if metadata is None:
            metadata = {}

        header_bytes = json.dumps(header).encode("utf-8")
        parent_bytes = json.dumps(parent_header).encode("utf-8")
        metadata_bytes = json.dumps(metadata).encode("utf-8")
        content_bytes = json.dumps(content).encode("utf-8")

        sig = self.sign([header_bytes, parent_bytes, metadata_bytes, content_bytes])

        parts = list(identities) + [
            DELIMITER,
            sig,
            header_bytes,
            parent_bytes,
            metadata_bytes,
            content_bytes,
        ]

        socket.send_multipart(parts)

    def parse_zmq_message(self, frames):
        """Parse a Jupyter wire protocol message from ZMQ frames."""
        # Find delimiter
        idx = -1
        for i, f in enumerate(frames):
            if f == DELIMITER:
                idx = i
                break
        if idx < 0:
            return None, None, None, None, None

        identities = frames[:idx]
        # signature = frames[idx + 1]
        header = json.loads(frames[idx + 2])
        parent_header = json.loads(frames[idx + 3])
        # metadata = json.loads(frames[idx + 4])
        content = json.loads(frames[idx + 5])

        return identities, header, parent_header, content, frames[idx + 2]

    def start_simple_process(self):
        """Start the Simple kernel process."""
        # Project root is two levels up from this script (tools/jupyter/)
        project_root = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
        kernel_script = os.path.join(project_root, "src", "app", "jupyter_kernel", "main.spl")

        self.process = subprocess.Popen(
            [self.simple_bin, kernel_script],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            bufsize=1,  # line-buffered
            cwd=project_root,
        )

        # Start thread to read responses from Simple kernel stdout
        self._reader_thread = threading.Thread(target=self._read_kernel_output, daemon=True)
        self._reader_thread.start()

    def _read_kernel_output(self):
        """Read JSON-lines from Simple kernel stdout and dispatch."""
        try:
            for line in self.process.stdout:
                line = line.strip()
                if not line:
                    continue
                try:
                    msg = json.loads(line)
                    self._handle_kernel_response(msg)
                except json.JSONDecodeError:
                    print(f"[wrapper] Invalid JSON from kernel: {line}", file=sys.stderr)
        except Exception as e:
            print(f"[wrapper] Reader thread error: {e}", file=sys.stderr)

    def _handle_kernel_response(self, msg):
        """Route kernel response to appropriate ZMQ socket."""
        channel = msg.get("channel", "")
        msg_type = msg.get("msg_type", "")
        parent_msg_id = msg.get("parent_msg_id", "")
        content = msg.get("content", {})

        # Look up the parent message info for this response
        with self._response_lock:
            parent_info = self._pending_responses.get(parent_msg_id, {})

        identities = parent_info.get("identities", [])
        parent_header = parent_info.get("header", {})

        if channel == "shell":
            self.send_zmq_message(self.shell_socket, identities, msg_type,
                                  content, parent_header)
        elif channel == "iopub":
            self.send_zmq_message(self.iopub_socket, [], msg_type,
                                  content, parent_header)
        elif channel == "control":
            self.send_zmq_message(self.control_socket, identities, msg_type,
                                  content, parent_header)

    def send_to_kernel(self, channel, msg_type, msg_id, session_id, content,
                       identities=None, header=None):
        """Send a JSON-line message to the Simple kernel process."""
        # Register the parent message for response routing
        with self._response_lock:
            self._pending_responses[msg_id] = {
                "identities": identities or [],
                "header": header or {},
            }

        msg = json.dumps({
            "channel": channel,
            "msg_type": msg_type,
            "msg_id": msg_id,
            "session": session_id,
            "content": content,
        })

        try:
            self.process.stdin.write(msg + "\n")
            self.process.stdin.flush()
        except (BrokenPipeError, OSError) as e:
            print(f"[wrapper] Failed to send to kernel: {e}", file=sys.stderr)

    def heartbeat_loop(self):
        """Echo heartbeat pings."""
        while True:
            try:
                data = self.heartbeat_socket.recv()
                self.heartbeat_socket.send(data)
            except zmq.ZMQError:
                break

    def shell_loop(self):
        """Handle shell channel messages."""
        while True:
            try:
                frames = self.shell_socket.recv_multipart()
                identities, header, parent_header, content, _ = self.parse_zmq_message(frames)
                if header is None:
                    continue

                msg_type = header.get("msg_type", "")
                msg_id = header.get("msg_id", "")
                session_id = header.get("session", "")

                self.send_to_kernel("shell", msg_type, msg_id, session_id,
                                    content, identities, header)
            except zmq.ZMQError:
                break

    def control_loop(self):
        """Handle control channel messages."""
        while True:
            try:
                frames = self.control_socket.recv_multipart()
                identities, header, parent_header, content, _ = self.parse_zmq_message(frames)
                if header is None:
                    continue

                msg_type = header.get("msg_type", "")
                msg_id = header.get("msg_id", "")
                session_id = header.get("session", "")

                self.send_to_kernel("control", msg_type, msg_id, session_id,
                                    content, identities, header)

                # If shutdown, wait for kernel to exit
                if msg_type == "shutdown_request":
                    time.sleep(0.5)
                    if self.process and self.process.poll() is None:
                        self.process.terminate()
                    sys.exit(0)
            except zmq.ZMQError:
                break

    def run(self):
        """Start all threads and the kernel process."""
        self.start_simple_process()

        # Start heartbeat in background
        hb_thread = threading.Thread(target=self.heartbeat_loop, daemon=True)
        hb_thread.start()

        # Start control in background
        ctrl_thread = threading.Thread(target=self.control_loop, daemon=True)
        ctrl_thread.start()

        # Run shell loop in main thread
        self.shell_loop()


def main():
    """Entry point: parse -f <connection_file> argument and start kernel."""
    connection_file = None
    args = sys.argv[1:]
    for i, arg in enumerate(args):
        if arg == "-f" and i + 1 < len(args):
            connection_file = args[i + 1]
            break

    if not connection_file:
        print("Usage: kernel_wrapper.py -f <connection_file>", file=sys.stderr)
        sys.exit(1)

    if not os.path.exists(connection_file):
        print(f"Error: Connection file not found: {connection_file}", file=sys.stderr)
        sys.exit(1)

    kernel = SimpleKernel(connection_file)
    kernel.run()


if __name__ == "__main__":
    main()
