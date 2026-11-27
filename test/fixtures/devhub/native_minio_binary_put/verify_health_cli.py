"""Check the real DevHub JSON health exit code against a failing HTTP server."""
import http.server
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import threading


def main():
    binary = Path(sys.argv[1]).resolve(strict=True)
    requests = []

    class Handler(http.server.BaseHTTPRequestHandler):
        def log_message(self, *_):
            pass

        def do_GET(self):
            requests.append(self.path)
            self.send_response(503)
            self.send_header("Content-Length", "0")
            self.end_headers()

    with http.server.ThreadingHTTPServer(("127.0.0.1", 0), Handler) as server:
        thread = threading.Thread(target=server.serve_forever, daemon=True)
        thread.start()
        try:
            with tempfile.TemporaryDirectory(prefix="devhub-minio-health-") as temporary:
                root = Path(temporary)
                config = root / ".config" / "devhub"
                config.mkdir(parents=True)
                (config / "auth.sdn").write_text(f"[minio]\nurl = http://127.0.0.1:{server.server_port}\n", encoding="utf-8")
                env = os.environ.copy()
                env.update(HOME=str(root), USERPROFILE=str(root), NO_COLOR="1")
                result = subprocess.run([str(binary), "minio", "health", "--json"], env=env, timeout=30, capture_output=True, text=True)
                print(result.stdout, end="")
                assert result.returncode == 1, f"unhealthy JSON command exited {result.returncode}"
                output = json.loads(result.stdout)
                assert output["alive"] is False and output["status"] == "HTTP 503", output
                assert requests == ["/minio/health/live"], requests
                print("PASS real DevHub unhealthy JSON result preserves nonzero exit")
        finally:
            server.shutdown()
            thread.join(timeout=5)


if __name__ == "__main__":
    main()
