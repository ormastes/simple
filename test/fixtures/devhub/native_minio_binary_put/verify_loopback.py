"""Run the actual native provider against an independent loopback S3 checker."""
import hashlib
import hmac
import http.server
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import threading


def main():
    binary = Path(sys.argv[1]).resolve(strict=True)
    observations = []
    failures = []
    attempts = []

    class Handler(http.server.BaseHTTPRequestHandler):
        def log_message(self, *_):
            pass

        def do_PUT(self):
            try:
                expected = b"" if self.path == "/bucket/empty.bin" else bytes([0, 128, 255, 65, 10])
                body = self.rfile.read(int(self.headers["Content-Length"]))
                attempts.append((self.path, len(body), hashlib.sha256(body).hexdigest()))
                assert body == expected, "request body changed binary octets"
                digest = hashlib.sha256(body).hexdigest()
                assert self.headers["x-amz-content-sha256"] == digest
                content_type = "application/x-fixture" if self.path == "/bucket/dir/../direct.bin" else "application/octet-stream"
                assert self.headers["Content-Type"] == content_type
                timestamp = self.headers["x-amz-date"]
                signed = "content-length;content-type;host;x-amz-content-sha256;x-amz-date"
                canonical_headers = "".join(f"{name}:{self.headers[name].strip()}\n" for name in signed.split(";"))
                canonical = "\n".join(["PUT", self.path, "", canonical_headers, signed, digest])
                scope = f"{timestamp[:8]}/us-east-1/s3/aws4_request"
                to_sign = "\n".join(["AWS4-HMAC-SHA256", timestamp, scope, hashlib.sha256(canonical.encode()).hexdigest()])
                signing = b"AWS4fixture-signing-key"
                for part in [timestamp[:8], "us-east-1", "s3", "aws4_request"]:
                    signing = hmac.new(signing, part.encode(), hashlib.sha256).digest()
                signature = hmac.new(signing, to_sign.encode(), hashlib.sha256).hexdigest()
                expected_auth = f"AWS4-HMAC-SHA256 Credential=fixture-access/{scope}, SignedHeaders={signed}, Signature={signature}"
                assert self.headers["Authorization"] == expected_auth, "Signature V4 mismatch"
                observations.append((self.path, len(body), digest))
                self.send_response(200)
                self.send_header("Content-Length", "8")
                self.end_headers()
                self.wfile.write(b"uploaded")
            except Exception as exc:
                failures.append(str(exc))
                self.send_response(400)
                self.send_header("Content-Length", "0")
                self.end_headers()

    with http.server.ThreadingHTTPServer(("127.0.0.1", 0), Handler) as server:
        thread = threading.Thread(target=server.serve_forever, daemon=True)
        thread.start()
        try:
            with tempfile.TemporaryDirectory(prefix="devhub-minio-loopback-") as temporary:
                root = Path(temporary)
                fixture = root / "binary.bin"
                fixture.write_bytes(bytes([0, 128, 255, 65, 10]))
                empty = root / "empty.bin"
                empty.write_bytes(b"")
                env = os.environ.copy()
                env.update(DEVHUB_MINIO_LOOPBACK_URL=f"http://127.0.0.1:{server.server_port}",
                           DEVHUB_MINIO_BINARY_FILE=str(fixture), DEVHUB_MINIO_EMPTY_FILE=str(empty),
                           TMPDIR=str(root), TEMP=str(root), TMP=str(root))
                result = subprocess.run([str(binary)], env=env, timeout=120, capture_output=True, text=True)
                print(result.stdout, end="")
                print(result.stderr, end="", file=sys.stderr)
                print(f"loopback native_exit={result.returncode} request_attempts={attempts} verified_requests={observations} failures={failures}")
                assert result.returncode == 0, f"native provider exited {result.returncode}"
                assert not failures, failures
                assert [p for p, _, _ in observations] == ["/bucket/dir/../direct.bin", "/bucket/file.bin", "/bucket/empty.bin"], observations
                assert not list(root.glob("simple-http-*")), "private HTTP staging was not cleaned"
                print("PASS independent loopback byte-exact payload, SHA256, SigV4 and request-count checks")
        finally:
            server.shutdown()
            thread.join(timeout=5)


if __name__ == "__main__":
    main()
