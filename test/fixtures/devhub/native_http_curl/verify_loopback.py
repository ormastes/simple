"""Check the actual Simple curl transport on an independent local HTTP server."""
import http.server
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import threading
import time


def main():
    binary = Path(sys.argv[1]).resolve(strict=True)
    attempts = []
    failures = []

    class Handler(http.server.BaseHTTPRequestHandler):
        def log_message(self, *_):
            pass

        def do_GET(self):
            attempts.append((self.path, 0))
            try:
                assert self.path == "/empty-get"
                assert self.headers.get("Content-Type") is None
                assert self.headers.get("Content-Length") in (None, "0")
                assert self.headers["Authorization"] == "Bearer fixture-token"
                reply = b"get accepted"
                self.send_response(200)
                self.send_header("Content-Length", str(len(reply)))
                self.end_headers()
                self.wfile.write(reply)
            except Exception as exc:
                failures.append(str(exc))
                self.send_response(400)
                self.send_header("Content-Length", "0")
                self.end_headers()

        def do_POST(self):
            body = self.rfile.read(int(self.headers["Content-Length"]))
            attempts.append((self.path, len(body)))
            try:
                if self.path == "/oversized":
                    self.send_response(200)
                    self.send_header("Content-Length", str(1048577))
                    self.end_headers()
                    return
                if self.path == "/stall":
                    time.sleep(32)
                    return
                if self.path == "/redirect":
                    self.send_response(302)
                    self.send_header("Location", "/must-not-follow")
                    self.send_header("Content-Length", "0")
                    self.end_headers()
                    return
                if self.path == "/form":
                    assert self.headers["Content-Type"] == "application/x-www-form-urlencoded"
                    assert body == b"client_secret=caf%C3%A9&scope=x%20y"
                    reply = b"form accepted"
                else:
                    assert self.path == "/utf8"
                    assert self.headers["Content-Type"] == "text/plain; charset=utf-8"
                    assert body == "café日本🙂".encode("utf-8")
                    reply = b"utf8 accepted"
                self.send_response(200)
                self.send_header("Content-Length", str(len(reply)))
                self.end_headers()
                self.wfile.write(reply)
            except Exception as exc:
                failures.append(str(exc))
                self.send_response(400)
                self.send_header("Content-Length", "0")
                self.end_headers()

    with http.server.ThreadingHTTPServer(("127.0.0.1", 0), Handler) as server:
        thread = threading.Thread(target=server.serve_forever, daemon=True)
        thread.start()
        try:
            with tempfile.TemporaryDirectory(prefix="devhub-http-staging-") as temporary:
                root = Path(temporary)
                env = os.environ.copy()
                env.update(DEVHUB_HTTP_LOOPBACK_URL=f"http://127.0.0.1:{server.server_port}",
                           TMPDIR=str(root), TEMP=str(root), TMP=str(root))
                started = time.monotonic()
                result = subprocess.run([str(binary)], env=env, timeout=150, capture_output=True, text=True)
                elapsed = time.monotonic() - started
                print(result.stdout, end="")
                print(result.stderr, end="", file=sys.stderr)
                print(f"loopback native_exit={result.returncode} request_attempts={attempts} failures={failures}")
                assert result.returncode == 0, f"native transport exited {result.returncode}"
                assert not failures, failures
                assert [path for path, _ in attempts] == ["/form", "/utf8", "/redirect", "/empty-get", "/oversized", "/stall"], attempts
                assert 25 <= elapsed < 55, f"bounded native HTTP run took {elapsed:.3f}s"
                assert not list(root.iterdir()), "private HTTP staging was not cleaned"
                print("PASS independent real POST form/UTF-8 and zero-request negative controls")
                print("PASS redirect refusal and private staging cleanup")
                print(f"PASS independent size refusal and deadline ({elapsed:.3f}s)")
        finally:
            server.shutdown()
            thread.join(timeout=5)


if __name__ == "__main__":
    main()
