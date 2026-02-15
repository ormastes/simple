#!/usr/bin/env python3
"""MCP Stdin Proxy - Bridges JSON-line and Content-Length framed MCP protocols.

The MCP SDK's StdioClientTransport sends JSON lines (newline-delimited JSON),
but the Simple MCP server expects Content-Length framed messages (LSP-style).
This proxy translates between the two formats:

  SDK (JSON lines) -> Proxy -> Content-Length framed -> Simple MCP server
  SDK (JSON lines) <- Proxy <- Content-Length framed <- Simple MCP server
"""
import os
import sys
import select
import signal
import subprocess
import time as _time_mod


def log(msg):
    """Debug log to file for diagnosing connection issues."""
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

    # Buffer for partial reads from stdin (SDK sends JSON lines)
    stdin_buf = b""

    # Buffer for partial reads from child stdout (Content-Length framed)
    child_buf = b""

    def read_json_line_from_stdin():
        """Read one JSON line from parent stdin (MCP SDK format).

        The MCP SDK StdioClientTransport sends messages as JSON + newline.
        Returns the JSON bytes (without trailing newline), or None on EOF.
        """
        nonlocal stdin_buf

        # Read until we have a complete line
        while b"\n" not in stdin_buf:
            ready = select.select([stdin_fd], [], [], 1.0)
            if not ready[0]:
                if proc.poll() is not None:
                    return None
                continue
            data = os.read(stdin_fd, 65536)
            if not data:
                return None
            stdin_buf += data

        idx = stdin_buf.index(b"\n")
        line = stdin_buf[:idx]
        stdin_buf = stdin_buf[idx + 1:]

        # Strip trailing \r if present
        if line.endswith(b"\r"):
            line = line[:-1]

        # Skip empty lines
        if not line.strip():
            return read_json_line_from_stdin()

        return line

    def wrap_content_length(json_bytes):
        """Wrap JSON bytes in Content-Length framing for the Simple MCP server.

        Format: Content-Length: N\r\n\r\nJSON\n
        The trailing \n is needed because Simple's input() reads until newline.
        """
        header = f"Content-Length: {len(json_bytes)}\r\n\r\n".encode("utf-8")
        return header + json_bytes + b"\n"

    def try_read_child_response():
        """Try to extract one Content-Length framed response from child_buf.

        Returns the JSON body bytes if a complete response is available,
        or None if more data is needed.
        """
        nonlocal child_buf

        # Need Content-Length header
        header_end_crlf = child_buf.find(b"\r\n\r\n")
        header_end_lf = child_buf.find(b"\n\n")

        if header_end_crlf >= 0:
            header_end = header_end_crlf
            separator_len = 4  # \r\n\r\n
        elif header_end_lf >= 0:
            header_end = header_end_lf
            separator_len = 2  # \n\n
        else:
            return None

        header = child_buf[:header_end].decode("utf-8", errors="replace")
        content_length = 0
        for hdr_line in header.split("\n"):
            hdr_line = hdr_line.strip().rstrip("\r")
            if hdr_line.lower().startswith("content-length:"):
                content_length = int(hdr_line.split(":", 1)[1].strip())

        if content_length == 0:
            # Skip malformed header
            child_buf = child_buf[header_end + separator_len:]
            return None

        body_start = header_end + separator_len
        body_end = body_start + content_length

        if len(child_buf) < body_end:
            return None  # Need more data

        body = child_buf[body_start:body_end]
        child_buf = child_buf[body_end:]

        # Skip any trailing newlines after body
        while child_buf.startswith(b"\n") or child_buf.startswith(b"\r\n"):
            if child_buf.startswith(b"\r\n"):
                child_buf = child_buf[2:]
            else:
                child_buf = child_buf[1:]

        return body

    def send_to_parent(body):
        """Send JSON body as a line to parent stdout (SDK format)."""
        json_line_out = body + b"\n"
        log(f"sending {len(json_line_out)} bytes to parent")
        if stdout_raw:
            stdout_raw.write(json_line_out)
        else:
            os.write(stdout_fd, json_line_out)

    def drain_child_responses():
        """Extract and forward all complete responses from child_buf."""
        while True:
            body = try_read_child_response()
            if body is None:
                break
            send_to_parent(body)

    stdin_closed = False
    stdin_eof_time = None
    import_time_monotonic = _time_mod.monotonic
    STDIN_EOF_TIMEOUT = 5.0
    log("entering main loop")
    try:
        while True:
            fds = [child_out_fd, child_err_fd]
            if not stdin_closed:
                fds.insert(0, stdin_fd)
            try:
                readable, _, _ = select.select(fds, [], [], 1.0)
            except (OSError, ValueError):
                log("select error, breaking")
                break

            for fd in readable:
                if fd == stdin_fd:
                    # Read JSON line from SDK
                    json_line = read_json_line_from_stdin()
                    if json_line is None:
                        log("stdin EOF, closing child stdin (letting child finish)")
                        try:
                            proc.stdin.close()
                        except Exception:
                            pass
                        stdin_closed = True
                        stdin_eof_time = import_time_monotonic()
                        break
                    log(f"forwarding {len(json_line)} bytes to child")
                    # Wrap in Content-Length framing for Simple MCP server
                    framed = wrap_content_length(json_line)
                    proc.stdin.write(framed)
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
                    # Read child stdout (Content-Length framed responses)
                    try:
                        data = os.read(child_out_fd, 65536)
                        if not data:
                            log("child stdout EOF")
                            cleanup()
                        log(f"child stdout: {len(data)} bytes")
                        child_buf += data
                        drain_child_responses()
                    except OSError:
                        log("child stdout OSError")
                        cleanup()

            # Check if child is still alive
            if proc.poll() is not None:
                log(f"child exited with code {proc.returncode}")
                # Drain remaining output
                while True:
                    try:
                        ready = select.select([child_out_fd], [], [], 0.1)
                        if ready[0]:
                            data = os.read(child_out_fd, 65536)
                            if data:
                                child_buf += data
                                drain_child_responses()
                            else:
                                break
                        else:
                            break
                    except OSError:
                        break
                break

            # If stdin closed, wait for child to finish (up to timeout)
            if stdin_closed and stdin_eof_time is not None:
                elapsed = import_time_monotonic() - stdin_eof_time
                if elapsed > STDIN_EOF_TIMEOUT:
                    log(f"stdin EOF timeout ({STDIN_EOF_TIMEOUT}s), terminating child")
                    break
    finally:
        cleanup()


if __name__ == "__main__":
    main()
