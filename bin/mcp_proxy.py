#!/usr/bin/env python3
"""MCP Stdin Proxy - Adds trailing newlines for Simple runtime compatibility.

The Simple runtime's input() function reads until newline. MCP protocol
doesn't guarantee a trailing newline after the JSON body. This proxy
reads MCP messages from Claude Code's stdin and forwards them with
a trailing newline to the Simple MCP server.
"""
import os
import sys
import select
import signal
import subprocess
import struct


def log(msg):
    """Debug log to file for diagnosing Claude Code connection issues."""
    try:
        with open("/tmp/mcp_proxy_debug.log", "a") as f:
            import datetime
            f.write(f"{datetime.datetime.now().isoformat()} {msg}\n")
            f.flush()
    except Exception:
        pass


def main():
    log("proxy starting")
    script_dir = os.path.dirname(os.path.abspath(__file__))
    runtime = os.path.join(script_dir, "release", "simple")
    mcp_main = os.path.join(script_dir, "..", "src", "app", "mcp", "main_lite.spl")

    log(f"runtime: {runtime}")
    log(f"mcp_main: {mcp_main}")
    log(f"runtime exists: {os.path.exists(runtime)}")
    log(f"mcp_main exists: {os.path.exists(mcp_main)}")

    env = os.environ.copy()
    env["SIMPLE_LIB"] = os.path.join(script_dir, "..", "src")
    env.setdefault("SIMPLE_VERSION", "unknown")

    try:
        proc = subprocess.Popen(
            [runtime, mcp_main],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            bufsize=0,
            env=env,
        )
        log(f"child started pid={proc.pid}")
    except Exception as e:
        log(f"FAILED to start child: {e}")
        sys.exit(1)

    stdin_fd = sys.stdin.fileno()
    stdout_fd = sys.stdout.fileno()
    child_out_fd = proc.stdout.fileno()
    child_err_fd = proc.stderr.fileno()

    # Make stdout unbuffered
    try:
        stdout_raw = os.fdopen(os.dup(stdout_fd), "wb", 0)
    except Exception:
        stdout_raw = None

    def cleanup(signum=None, frame=None):
        try:
            proc.terminate()
        except Exception:
            pass
        os._exit(0)

    signal.signal(signal.SIGTERM, cleanup)
    signal.signal(signal.SIGINT, cleanup)

    # Buffer for partial reads from Claude Code's stdin
    stdin_buf = b""

    def read_mcp_message_from_stdin():
        """Read one complete MCP message from parent stdin, return raw bytes."""
        nonlocal stdin_buf

        # Read until we have a complete header (ends with \r\n\r\n)
        while b"\r\n\r\n" not in stdin_buf:
            ready = select.select([stdin_fd], [], [], 1.0)
            if not ready[0]:
                # Check if child is still alive
                if proc.poll() is not None:
                    return None
                continue
            data = os.read(stdin_fd, 65536)
            if not data:
                return None
            stdin_buf += data

        # Parse header
        hdr_end = stdin_buf.index(b"\r\n\r\n") + 4
        header = stdin_buf[:hdr_end]
        stdin_buf = stdin_buf[hdr_end:]

        # Extract content length
        content_length = 0
        for line in header.decode("utf-8", errors="replace").split("\r\n"):
            if line.lower().startswith("content-length:"):
                content_length = int(line.split(":", 1)[1].strip())

        if content_length == 0:
            return header  # Forward header as-is

        # Read body
        while len(stdin_buf) < content_length:
            ready = select.select([stdin_fd], [], [], 1.0)
            if not ready[0]:
                if proc.poll() is not None:
                    return None
                continue
            data = os.read(stdin_fd, 65536)
            if not data:
                return None
            stdin_buf += data

        body = stdin_buf[:content_length]
        stdin_buf = stdin_buf[content_length:]

        # Skip any trailing \r\n after body (some clients send it)
        while stdin_buf.startswith(b"\r\n") or stdin_buf.startswith(b"\n"):
            stdin_buf = stdin_buf[1:] if stdin_buf.startswith(b"\n") else stdin_buf[2:]

        return header + body

    log("entering main loop")
    try:
        while True:
            fds = [stdin_fd, child_out_fd, child_err_fd]
            try:
                readable, _, _ = select.select(fds, [], [], 1.0)
            except (OSError, ValueError):
                log("select error, breaking")
                break

            for fd in readable:
                if fd == stdin_fd:
                    # Read complete MCP message from Claude Code
                    msg = read_mcp_message_from_stdin()
                    if msg is None:
                        log("stdin EOF, cleaning up")
                        cleanup()
                    log(f"forwarding {len(msg)} bytes to child")
                    # Forward to child with trailing newline for input() compatibility
                    proc.stdin.write(msg + b"\n")
                    proc.stdin.flush()

                elif fd == child_err_fd:
                    # Log child stderr
                    try:
                        err_data = os.read(child_err_fd, 65536)
                        if err_data:
                            log(f"child stderr: {err_data.decode('utf-8', errors='replace')[:200]}")
                    except OSError:
                        pass

                elif fd == child_out_fd:
                    # Forward child stdout directly to parent stdout
                    try:
                        data = os.read(child_out_fd, 65536)
                        if not data:
                            log("child stdout EOF")
                            cleanup()
                        log(f"child stdout: {len(data)} bytes")
                        if stdout_raw:
                            stdout_raw.write(data)
                        else:
                            os.write(stdout_fd, data)
                    except OSError:
                        log("child stdout OSError")
                        cleanup()

            # Check if child is still alive
            if proc.poll() is not None:
                # Drain remaining output
                while True:
                    try:
                        ready = select.select([child_out_fd], [], [], 0.1)
                        if ready[0]:
                            data = os.read(child_out_fd, 65536)
                            if data:
                                if stdout_raw:
                                    stdout_raw.write(data)
                                else:
                                    os.write(stdout_fd, data)
                            else:
                                break
                        else:
                            break
                    except OSError:
                        break
                break
    finally:
        cleanup()


if __name__ == "__main__":
    main()
