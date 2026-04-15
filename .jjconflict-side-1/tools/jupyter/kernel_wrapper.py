#!/usr/bin/env python3
"""
Simple Language Jupyter Kernel Wrapper

Thin Python bridge between Jupyter's ZMQ wire protocol and the Simple kernel
process (src/app/jupyter_kernel/main.spl) which communicates via JSON-lines
on stdin/stdout.

Architecture:
    Jupyter Client (browser/console)
        |
        v  (ZMQ wire protocol)
    kernel_wrapper.py (this file)
        |
        v  (stdin/stdout JSON-lines)
    Simple Kernel (bin/simple run src/app/jupyter_kernel/main.spl)
"""

import argparse
import hashlib
import hmac
import json
import os
import signal
import subprocess
import sys
import threading
import time
import uuid
from glob import glob

import zmq

# ---------------------------------------------------------------------------
# Jupyter wire protocol helpers
# ---------------------------------------------------------------------------

DELIMITER = b"<IDS|MSG>"
PROTOCOL_VERSION = "5.4"


def find_project_root():
    """Walk up from this script to find project root (contains bin/)."""
    d = os.path.dirname(os.path.abspath(__file__))
    for _ in range(10):
        if os.path.isdir(os.path.join(d, "bin")):
            return d
        d = os.path.dirname(d)
    return os.getcwd()


def find_simple_runtime(project_root):
    """Resolve the preferred Simple runtime for the current checkout."""
    candidates = [
        os.path.join(project_root, "src", "compiler_rust", "target", "release", "simple"),
        os.path.join(project_root, "src", "compiler_rust", "target", "bootstrap", "simple"),
        os.path.join(project_root, "bin", "simple"),
        os.path.join(project_root, "bin", "release", "simple"),
    ]
    candidates.extend(sorted(glob(os.path.join(project_root, "bin", "release", "*", "simple"))))

    for candidate in candidates:
        if os.path.isfile(candidate) and os.access(candidate, os.X_OK):
            return candidate

    return os.path.join(project_root, "bin", "simple")


def new_header(msg_type, session):
    """Create a Jupyter message header."""
    return {
        "msg_id": str(uuid.uuid4()),
        "msg_type": msg_type,
        "session": session,
        "date": time.strftime("%Y-%m-%dT%H:%M:%S.000000Z", time.gmtime()),
        "username": "simple_kernel",
        "version": PROTOCOL_VERSION,
    }


def sign(parts, key):
    """HMAC-SHA256 signature of message parts."""
    if not key:
        return b""
    h = hmac.new(key, digestmod=hashlib.sha256)
    for p in parts:
        h.update(p)
    return h.hexdigest().encode("ascii")


def send_message(socket, idents, header, parent_header, metadata, content, key):
    """Send a Jupyter ZMQ multipart message."""
    header_b = json.dumps(header).encode("utf-8")
    parent_b = json.dumps(parent_header).encode("utf-8")
    meta_b = json.dumps(metadata).encode("utf-8")
    content_b = json.dumps(content).encode("utf-8")

    sig = sign([header_b, parent_b, meta_b, content_b], key)

    parts = list(idents) + [DELIMITER, sig, header_b, parent_b, meta_b, content_b]
    socket.send_multipart(parts)


def recv_message(socket):
    """Receive and parse a Jupyter ZMQ multipart message."""
    parts = socket.recv_multipart()

    # Find delimiter
    idx = parts.index(DELIMITER)
    idents = parts[:idx]
    # sig = parts[idx + 1]
    header = json.loads(parts[idx + 2])
    parent_header = json.loads(parts[idx + 3])
    metadata = json.loads(parts[idx + 4])
    content = json.loads(parts[idx + 5])

    return idents, header, parent_header, metadata, content


# ---------------------------------------------------------------------------
# Kernel process management
# ---------------------------------------------------------------------------

class SimpleKernel:
    """Manages the Simple kernel subprocess and message bridging."""

    def __init__(self, connection_file):
        with open(connection_file) as f:
            self.conn = json.load(f)

        self.key = self.conn.get("key", "").encode("utf-8") or None
        self.transport = self.conn.get("transport", "tcp")
        self.ip = self.conn.get("ip", "127.0.0.1")
        self.session = str(uuid.uuid4())
        self.project_root = find_project_root()

        self.proc = None
        self.proc_lock = threading.Lock()
        self.stdout_lines = []
        self.stdout_event = threading.Event()

    def _addr(self, port):
        return f"{self.transport}://{self.ip}:{port}"

    def start(self):
        """Start ZMQ sockets and Simple kernel subprocess."""
        self.ctx = zmq.Context()

        # Shell (ROUTER)
        self.shell_sock = self.ctx.socket(zmq.ROUTER)
        self.shell_sock.bind(self._addr(self.conn["shell_port"]))

        # IOPub (PUB)
        self.iopub_sock = self.ctx.socket(zmq.PUB)
        self.iopub_sock.bind(self._addr(self.conn["iopub_port"]))

        # Stdin (ROUTER) - not actively used
        self.stdin_sock = self.ctx.socket(zmq.ROUTER)
        self.stdin_sock.bind(self._addr(self.conn["stdin_port"]))

        # Control (ROUTER)
        self.control_sock = self.ctx.socket(zmq.ROUTER)
        self.control_sock.bind(self._addr(self.conn["control_port"]))

        # Heartbeat (REP)
        self.hb_sock = self.ctx.socket(zmq.REP)
        self.hb_sock.bind(self._addr(self.conn["hb_port"]))

        # Start Simple kernel process
        kernel_path = os.path.join(self.project_root, "src", "app", "jupyter_kernel", "main.spl")
        simple_bin = find_simple_runtime(self.project_root)

        self.proc = subprocess.Popen(
            [simple_bin, "run", kernel_path],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            cwd=self.project_root,
        )

        # Start background threads
        self.hb_thread = threading.Thread(target=self._heartbeat_loop, daemon=True)
        self.hb_thread.start()

        self.stdout_thread = threading.Thread(target=self._stdout_reader, daemon=True)
        self.stdout_thread.start()

        self.control_thread = threading.Thread(target=self._control_loop, daemon=True)
        self.control_thread.start()

    def _heartbeat_loop(self):
        """Echo heartbeat messages."""
        while True:
            try:
                data = self.hb_sock.recv()
                self.hb_sock.send(data)
            except zmq.ZMQError:
                break

    def _stdout_reader(self):
        """Read JSON-lines from kernel stdout in background."""
        try:
            for raw_line in self.proc.stdout:
                line = raw_line.decode("utf-8", errors="replace").strip()
                if line:
                    self.stdout_lines.append(line)
                    self.stdout_event.set()
        except (ValueError, OSError):
            pass

    def _control_loop(self):
        """Handle control channel messages (shutdown, etc.)."""
        while True:
            try:
                idents, header, parent, meta, content = recv_message(self.control_sock)
                if header["msg_type"] == "shutdown_request":
                    reply_header = new_header("shutdown_reply", self.session)
                    reply_content = {"status": "ok", "restart": content.get("restart", False)}
                    send_message(self.control_sock, idents, reply_header, header, {}, reply_content, self.key)
                    self.shutdown()
                    break
            except zmq.ZMQError:
                break

    def send_to_kernel(self, msg):
        """Send a JSON-line to the kernel subprocess stdin."""
        with self.proc_lock:
            if self.proc and self.proc.stdin:
                line = json.dumps(msg) + "\n"
                self.proc.stdin.write(line.encode("utf-8"))
                self.proc.stdin.flush()

    def read_from_kernel(self, timeout=30):
        """Read a JSON-line response from kernel stdout."""
        deadline = time.time() + timeout
        while time.time() < deadline:
            if self.stdout_lines:
                line = self.stdout_lines.pop(0)
                try:
                    return json.loads(line)
                except json.JSONDecodeError:
                    continue
            self.stdout_event.clear()
            self.stdout_event.wait(timeout=0.1)
        return None

    def read_all_from_kernel(self, timeout=5):
        """Read all pending responses within timeout."""
        msgs = []
        deadline = time.time() + timeout
        while time.time() < deadline:
            msg = self.read_from_kernel(timeout=0.5)
            if msg:
                msgs.append(msg)
            else:
                break
        return msgs

    def handle_shell_message(self, idents, header, parent, meta, content):
        """Bridge a shell message from Jupyter to Simple kernel."""
        msg_type = header["msg_type"]

        # Send to Simple kernel as JSON-line
        kernel_msg = {
            "channel": "shell",
            "msg_type": msg_type,
            "msg_id": header["msg_id"],
            "session": header.get("session", self.session),
            "content": content,
        }

        # For execute_request, include code in the top-level for extract_field
        if msg_type == "execute_request":
            kernel_msg["code"] = content.get("code", "")

        if msg_type == "is_complete_request":
            kernel_msg["code"] = content.get("code", "")

        self.send_to_kernel(kernel_msg)

        # Read responses and forward to Jupyter
        responses = self.read_all_from_kernel(timeout=30)
        for resp in responses:
            resp_channel = resp.get("channel", "shell")
            resp_type = resp.get("msg_type", "")
            resp_content = resp.get("content", {})

            resp_header = new_header(resp_type, self.session)

            if resp_channel == "iopub":
                send_message(self.iopub_sock, [], resp_header, header, {}, resp_content, self.key)
            else:
                send_message(self.shell_sock, idents, resp_header, header, {}, resp_content, self.key)

    def run(self):
        """Main loop: receive and handle shell messages."""
        while True:
            try:
                idents, header, parent, meta, content = recv_message(self.shell_sock)
                self.handle_shell_message(idents, header, parent, meta, content)
            except zmq.ZMQError:
                break
            except KeyboardInterrupt:
                break

        self.shutdown()

    def shutdown(self):
        """Shut down kernel process and ZMQ sockets."""
        # Send shutdown to kernel
        shutdown_msg = {
            "channel": "shell",
            "msg_type": "shutdown_request",
            "msg_id": str(uuid.uuid4()),
            "session": self.session,
            "content": {"restart": False},
        }
        try:
            self.send_to_kernel(shutdown_msg)
        except (BrokenPipeError, OSError):
            pass

        # Kill process
        if self.proc:
            try:
                self.proc.terminate()
                self.proc.wait(timeout=5)
            except (subprocess.TimeoutExpired, OSError):
                try:
                    self.proc.kill()
                except OSError:
                    pass

        # Close sockets
        for sock in [self.shell_sock, self.iopub_sock, self.stdin_sock,
                      self.control_sock, self.hb_sock]:
            try:
                sock.close()
            except Exception:
                pass
        try:
            self.ctx.term()
        except Exception:
            pass

        sys.exit(0)


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(description="Simple Language Jupyter Kernel Wrapper")
    parser.add_argument("-f", "--connection-file", required=True,
                        help="Path to Jupyter connection file")
    args = parser.parse_args()

    kernel = SimpleKernel(args.connection_file)

    # Handle SIGTERM/SIGINT
    def signal_handler(sig, frame):
        kernel.shutdown()

    signal.signal(signal.SIGTERM, signal_handler)
    signal.signal(signal.SIGINT, signal_handler)

    kernel.start()
    kernel.run()


if __name__ == "__main__":
    main()
