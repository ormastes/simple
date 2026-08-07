#!/usr/bin/env python3
"""Jupyter ZMQ transport bridge for the Simple kernel.

Sanctioned Python exception (see doc/03_plan/agent_tasks/
notebook_lanes_parallel_plan_2026-08-07.md, Stream P / P0): this file is
TRANSPORT ONLY. It does not interpret, validate, or branch on the contents of
any Simple-language payload (cell code, output text, tracebacks, ...) -- it
only reads/writes the small set of Jupyter wire-protocol envelope fields
(msg_id, msg_type, session, parent, content-as-opaque-JSON-blob) needed to
route a message. All language-level behavior lives in the existing Simple
kernel process (src/app/jupyter_kernel/main.spl), which this script spawns
as a subprocess and talks to over stdin/stdout JSON-lines.

Responsibilities:
  1. Parse the Jupyter connection file (5 ports: shell, iopub, stdin,
     control, hb).
  2. Open the 5 ZMQ sockets the wire protocol requires.
  3. Sign outgoing messages / verify incoming messages with HMAC-SHA256
     (the connection file's "key" + "signature_scheme").
  4. Answer heartbeat pings.
  5. Bridge ZMQ multipart messages <-> the kernel's stdin/stdout
     JSON-lines protocol (see src/app/jupyter_kernel/main.spl header
     comment for the line format).

Usage: kernel_wrapper.py -f <connection_file>
"""

import hashlib
import hmac
import json
import os
import queue
import subprocess
import sys
import threading
import time
import uuid
from datetime import datetime, timezone

try:
    import zmq
except ImportError:  # pragma: no cover - dependency documented in guide
    sys.stderr.write(
        "kernel_wrapper.py: pyzmq is required (pip install pyzmq)\n"
    )
    raise

DELIM = b"<IDS|MSG>"
PROTOCOL_VERSION = "5.3"

_MARKER = os.path.join("src", "app", "jupyter_kernel", "main.spl")


def find_repo_root():
    """Locate the Simple repo root.

    `jupyter kernelspec install` copies this script out of the repo tree
    (into ~/.local/share/jupyter/kernels/simple/), so the root can no
    longer be derived from __file__ after install. Precedence:
      1. SIMPLE_REPO_ROOT env var, if it points at a real checkout.
      2. Walk upward from the launch cwd (Jupyter runs kernels with the
         notebook/server's cwd, which is expected to be the repo root or
         a subdirectory of it) looking for the marker file.
      3. Walk upward from this script's own location, for the in-tree,
         not-yet-installed case (`tools/jupyter/kernel_wrapper.py`).
    """
    env_root = os.environ.get("SIMPLE_REPO_ROOT")
    if env_root and os.path.exists(os.path.join(env_root, _MARKER)):
        return os.path.abspath(env_root)

    for start in (os.getcwd(), os.path.dirname(os.path.abspath(__file__))):
        current = start
        while True:
            if os.path.exists(os.path.join(current, _MARKER)):
                return current
            parent = os.path.dirname(current)
            if parent == current:
                break
            current = parent

    raise SystemExit(
        "kernel_wrapper.py: cannot locate the Simple repo root "
        "(set SIMPLE_REPO_ROOT or launch Jupyter from within the repo)"
    )


REPO_ROOT = find_repo_root()


def find_simple_runtime():
    """Locate the Simple runtime binary the same way the kernel itself does."""
    candidates = [
        "bin/simple",
        "bin/release/aarch64-apple-darwin-macho/simple",
        "bin/release/macos-arm64/simple",
        "bin/release/darwin-aarch64/simple",
        "bin/release/macos-x86_64/simple",
        "bin/release/linux-x86_64/simple",
        "bin/release/x86_64-unknown-linux-gnu/simple",
    ]
    for rel in candidates:
        path = os.path.join(REPO_ROOT, rel)
        if os.path.exists(path):
            return path
    return os.path.join(REPO_ROOT, "bin/simple")


def find_kernel_entry():
    entry = os.path.join(REPO_ROOT, "src/app/jupyter_kernel/main.spl")
    if os.path.exists(entry):
        return entry
    raise SystemExit(
        "kernel_wrapper.py: cannot find src/app/jupyter_kernel/main.spl"
    )


def utc_now_iso():
    return datetime.now(timezone.utc).isoformat()


class HMACSigner:
    """Wraps the connection file's signing key / scheme."""

    def __init__(self, key, scheme):
        self.key = key.encode("utf-8") if key else b""
        scheme = (scheme or "hmac-sha256").lower()
        if scheme in ("", "hmac-sha256"):
            self.digestmod = hashlib.sha256
        elif scheme == "hmac-sha1":
            self.digestmod = hashlib.sha1
        elif scheme == "hmac-md5":
            self.digestmod = hashlib.md5
        else:
            raise SystemExit(f"unsupported signature_scheme: {scheme}")

    @property
    def enabled(self):
        return len(self.key) > 0

    def sign(self, frames):
        if not self.enabled:
            return b""
        h = hmac.new(self.key, digestmod=self.digestmod)
        for frame in frames:
            h.update(frame)
        return h.hexdigest().encode("ascii")

    def verify(self, signature, frames):
        if not self.enabled:
            return True
        expected = self.sign(frames)
        return hmac.compare_digest(expected, signature)


def encode(obj):
    return json.dumps(obj if obj is not None else {}).encode("utf-8")


def decode(raw):
    if not raw:
        return {}
    return json.loads(raw.decode("utf-8"))


class WireMessage:
    """A parsed Jupyter multipart message."""

    __slots__ = (
        "identities",
        "header",
        "parent_header",
        "metadata",
        "content",
        "buffers",
    )

    def __init__(self, identities, header, parent_header, metadata, content, buffers):
        self.identities = identities
        self.header = header
        self.parent_header = parent_header
        self.metadata = metadata
        self.content = content
        self.buffers = buffers


def parse_multipart(frames, signer):
    """Split a raw ZMQ multipart message into identities + envelope."""
    try:
        delim_idx = frames.index(DELIM)
    except ValueError:
        return None
    identities = frames[:delim_idx]
    signature = frames[delim_idx + 1]
    body = frames[delim_idx + 2 : delim_idx + 6]
    if len(body) < 4:
        return None
    header_raw, parent_raw, metadata_raw, content_raw = body
    if not signer.verify(signature, [header_raw, parent_raw, metadata_raw, content_raw]):
        sys.stderr.write("kernel_wrapper.py: signature verification failed, dropping message\n")
        return None
    buffers = frames[delim_idx + 6 :]
    return WireMessage(
        identities,
        decode(header_raw),
        decode(parent_raw),
        decode(metadata_raw),
        decode(content_raw),
        buffers,
    )


def build_header(msg_type, session):
    return {
        "msg_id": str(uuid.uuid4()),
        "session": session,
        "username": "kernel",
        "date": utc_now_iso(),
        "msg_type": msg_type,
        "version": PROTOCOL_VERSION,
    }


def build_multipart(identities, header, parent_header, metadata, content, signer):
    frames = [encode(header), encode(parent_header), encode(metadata or {}), encode(content)]
    signature = signer.sign(frames)
    return list(identities) + [DELIM, signature] + frames


class KernelProcess:
    """Owns the Simple kernel subprocess and its JSON-lines stdin/stdout."""

    def __init__(self):
        runtime = find_simple_runtime()
        entry = find_kernel_entry()
        self.proc = subprocess.Popen(
            [runtime, "run", entry],
            cwd=REPO_ROOT,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=None,  # inherit -- diagnostics only, never protocol data
            bufsize=1,
            universal_newlines=True,
        )
        self._out_q = queue.Queue()
        self._reader = threading.Thread(target=self._read_loop, daemon=True)
        self._reader.start()

    def _read_loop(self):
        try:
            for line in self.proc.stdout:
                line = line.rstrip("\n")
                if line:
                    self._out_q.put(line)
        except Exception:
            pass
        finally:
            self._out_q.put(None)  # sentinel: process closed stdout

    def send(self, obj):
        line = json.dumps(obj)
        self.proc.stdin.write(line + "\n")
        self.proc.stdin.flush()

    def poll_line(self, timeout):
        try:
            return self._out_q.get(timeout=timeout)
        except queue.Empty:
            return "__TIMEOUT__"

    def interrupt(self):
        # Best-effort SIGINT relay for control-channel interrupt_request.
        try:
            self.proc.send_signal(subprocess.signal.SIGINT)
        except Exception:
            pass

    def shutdown(self):
        try:
            if self.proc.stdin:
                self.proc.stdin.close()
        except Exception:
            pass
        try:
            self.proc.wait(timeout=5)
        except Exception:
            try:
                self.proc.terminate()
            except Exception:
                pass


class Bridge:
    def __init__(self, connection_file):
        with open(connection_file, "r", encoding="utf-8") as f:
            self.conn = json.load(f)

        self.session_id = str(uuid.uuid4())
        self.signer = HMACSigner(self.conn.get("key", ""), self.conn.get("signature_scheme"))

        self.ctx = zmq.Context.instance()
        transport = self.conn.get("transport", "tcp")
        ip = self.conn.get("ip", "127.0.0.1")

        def addr(port_key):
            return f"{transport}://{ip}:{self.conn[port_key]}"

        self.shell_sock = self.ctx.socket(zmq.ROUTER)
        self.shell_sock.bind(addr("shell_port"))

        self.control_sock = self.ctx.socket(zmq.ROUTER)
        self.control_sock.bind(addr("control_port"))

        self.stdin_sock = self.ctx.socket(zmq.ROUTER)
        self.stdin_sock.bind(addr("stdin_port"))

        self.iopub_sock = self.ctx.socket(zmq.PUB)
        self.iopub_sock.bind(addr("iopub_port"))

        self.hb_sock = self.ctx.socket(zmq.REP)
        self.hb_sock.bind(addr("hb_port"))

        self.kernel = KernelProcess()

        # msg_id -> (identities, header, channel) for routing kernel replies
        # back to the right ZMQ client + channel.
        self._pending = {}
        self._lock = threading.Lock()
        self._running = True

        self._hb_thread = threading.Thread(target=self._heartbeat_loop, daemon=True)
        self._hb_thread.start()

    def _heartbeat_loop(self):
        while self._running:
            try:
                msg = self.hb_sock.recv()
                self.hb_sock.send(msg)
            except zmq.ZMQError:
                break

    def _forward_to_kernel(self, channel, wire_msg):
        header = wire_msg.header
        msg_type = header.get("msg_type", "")
        msg_id = header.get("msg_id", "")

        # control-channel interrupt_request (design §5.1/§5.3): SIGINT is a
        # best-effort, process-level escalation the kernel subprocess itself
        # cannot trigger from inside its own stdin loop -- fire it here, in
        # addition to (not instead of) relaying the request below. The
        # kernel's own interrupt_reply, produced by its cooperative
        # NotebookExecutor.interrupt() handling and relayed like every other
        # reply, is the source of truth for the reply status; the wrapper
        # never fabricates one.
        if msg_type == "interrupt_request":
            self.kernel.interrupt()

        with self._lock:
            self._pending[msg_id] = (wire_msg.identities, header, channel)

        line = {
            "channel": channel,
            "msg_type": msg_type,
            "msg_id": msg_id,
            "session": header.get("session", self.session_id),
            "content": wire_msg.content,
        }
        self.kernel.send(line)

    def _emit_from_kernel(self, reply):
        channel = reply.get("channel", "shell")
        msg_type = reply.get("msg_type", "")
        parent_msg_id = reply.get("parent_msg_id", "")
        content = reply.get("content", {})

        with self._lock:
            pending = self._pending.get(parent_msg_id)

        parent_header = pending[1] if pending else {}
        session = parent_header.get("session", self.session_id) if pending else self.session_id
        reply_header = build_header(msg_type, session)

        if channel == "iopub":
            topic = msg_type.encode("utf-8")
            frames = [topic, DELIM, self.signer.sign(
                [encode(reply_header), encode(parent_header), encode({}), encode(content)]
            ), encode(reply_header), encode(parent_header), encode({}), encode(content)]
            self.iopub_sock.send_multipart(frames)
            return

        # shell/control/stdin replies route back to the identities captured
        # when the originating request came in.
        identities = pending[0] if pending else []
        sock = self.shell_sock if channel != "control" else self.control_sock
        frames = build_multipart(identities, reply_header, parent_header, {}, content, self.signer)
        sock.send_multipart(frames)

        # kernel_info/execute/is_complete/shutdown/comm_info replies close
        # out the request; drop bookkeeping once the shell/control reply
        # (not the iopub status chatter) has gone out.
        if channel in ("shell", "control") and pending is not None:
            with self._lock:
                self._pending.pop(parent_msg_id, None)

    def run(self):
        poller = zmq.Poller()
        poller.register(self.shell_sock, zmq.POLLIN)
        poller.register(self.control_sock, zmq.POLLIN)
        poller.register(self.stdin_sock, zmq.POLLIN)

        try:
            while self._running:
                socks = dict(poller.poll(timeout=50))

                if self.shell_sock in socks:
                    frames = self.shell_sock.recv_multipart()
                    msg = parse_multipart(frames, self.signer)
                    if msg is not None:
                        self._forward_to_kernel("shell", msg)

                if self.control_sock in socks:
                    frames = self.control_sock.recv_multipart()
                    msg = parse_multipart(frames, self.signer)
                    if msg is not None:
                        self._forward_to_kernel("control", msg)

                # stdin_sock: input_request/input_reply not supported by the
                # Simple kernel today; drain to avoid a stuck client, no-op.
                if self.stdin_sock in socks:
                    self.stdin_sock.recv_multipart()

                line = self.kernel.poll_line(0)
                while line not in (None, "__TIMEOUT__"):
                    try:
                        reply = json.loads(line)
                    except json.JSONDecodeError:
                        line = self.kernel.poll_line(0)
                        continue
                    self._emit_from_kernel(reply)
                    if reply.get("msg_type") == "shutdown_reply":
                        self._running = False
                    line = self.kernel.poll_line(0)
                if line is None:
                    # kernel subprocess closed stdout -- exit the bridge.
                    break
        except KeyboardInterrupt:
            pass
        finally:
            self.kernel.shutdown()


def parse_args(argv):
    connection_file = None
    i = 0
    while i < len(argv):
        arg = argv[i]
        if arg in ("-f", "--connection-file") and i + 1 < len(argv):
            connection_file = argv[i + 1]
            i += 2
        elif arg.startswith("--connection-file="):
            connection_file = arg.split("=", 1)[1]
            i += 1
        else:
            i += 1
    return connection_file


def main():
    connection_file = parse_args(sys.argv[1:])
    if not connection_file:
        sys.stderr.write("usage: kernel_wrapper.py -f <connection_file>\n")
        return 1
    bridge = Bridge(connection_file)
    bridge.run()
    return 0


if __name__ == "__main__":
    sys.exit(main())
