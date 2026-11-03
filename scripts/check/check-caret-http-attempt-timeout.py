#!/usr/bin/env python3
"""Exercise real Simple adapter owners; requires a qualified POSIX runtime.

No seed/build/fallback. The server delays responses beyond the adapter budget.
The request ledger detects missing execution, retries, and negative-timeout I/O.
"""
import argparse
from collections import Counter
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import os
from pathlib import Path
import subprocess
import threading
import time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--runtime", type=Path, required=True)
    args = parser.parse_args()
    runtime = args.runtime.resolve(strict=True)
    root = Path(__file__).resolve().parents[2]
    ledger = Counter()
    lock = threading.Lock()

    class Handler(BaseHTTPRequestHandler):
        def do_POST(self):
            body = self.rfile.read(int(self.headers.get("Content-Length", "0")))
            with lock:
                ledger[self.path] += 1
            if self.path == "/slow":
                time.sleep(2)
            try:
                self.send_response(200)
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)
            except (BrokenPipeError, ConnectionResetError):
                pass  # Expected: the timed request disconnected.

        def log_message(self, *unused):
            pass

    server = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    environment = os.environ.copy()
    environment["CARET_TIMEOUT_TEST_URL"] = f"http://127.0.0.1:{server.server_port}"
    try:
        result = subprocess.run(
            [str(runtime), "test", "test/03_system/app/llm_caret/feature/llm_caret_attempt_timeout_spec.spl"],
            cwd=root, env=environment, timeout=120, check=False,
        )
        if result.returncode:
            raise SystemExit(result.returncode)
        with lock:
            observed = dict(ledger)
        if observed != {"/slow": 3, "/echo": 1}:
            raise SystemExit(f"FAIL: real adapter request ledger {observed!r}")
        print("PASS: three bounded real adapters, UTF8 echo, and no negative-timeout request")
    finally:
        server.shutdown()
        server.server_close()
        thread.join(timeout=2)


if __name__ == "__main__":
    main()
