#!/usr/bin/env python3
import importlib.util
import pathlib
import sys
import threading
import unittest
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer


MODULE_PATH = pathlib.Path(__file__).with_name("live_h2load_compare.py")
SPEC = importlib.util.spec_from_file_location("live_h2load_compare", MODULE_PATH)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


GOOD = """finished in 10.00s, 321.50 req/s, 1.00MB/s
requests: 3215 total, 3215 started, 3215 done, 3200 succeeded, 15 failed, 5 errored, 10 timeout
time for request: 100us 2.50ms 1.00ms 70.00%
 50% 2.00ms
 95% 4.50ms
 99% 8.00ms
"""


class ParserContract(unittest.TestCase):
    def test_complete_output(self):
        result = MODULE.parse_h2load(GOOD)
        self.assertEqual(result.succeeded, 3200)
        self.assertEqual(result.failed, 15)
        # h2load reports request timing as min, max, mean, sd, sd%; the
        # evidence row must retain the mean rather than accidentally the max.
        self.assertEqual(result.mean_latency_us, 1000.0)
        self.assertEqual(result.p99_us, 8000.0)

    def test_missing_request_row_fails_closed(self):
        with self.assertRaisesRegex(ValueError, "incomplete-h2load-output"):
            MODULE.parse_h2load("finished in 1s, 20 req/s")

    def test_inconsistent_counts_fail_closed(self):
        bad = GOOD.replace("3215 done, 3200 succeeded, 15 failed", "3215 done, 3200 succeeded, 14 failed")
        with self.assertRaisesRegex(ValueError, "inconsistent-h2load-request-counts"):
            MODULE.parse_h2load(bad)

    def test_protocol_path_query_contract(self):
        self.assertEqual(MODULE.target_protocol("https://127.0.0.1:8443/a?q=1"),
                         ("https", "/a", "q=1"))
        with self.assertRaisesRegex(ValueError, "target-url"):
            MODULE.target_protocol("ftp://127.0.0.1/a")

    def test_request_log_provides_latency_distribution(self):
        values = MODULE.parse_h2load_log("0\t200\t100\n1\t204\t300\n2\t200\t200\n")
        self.assertEqual(values, [100, 200, 300])
        self.assertEqual(MODULE.percentile(values, 0.50), 200.0)

    def test_request_log_rejects_http_error(self):
        with self.assertRaisesRegex(ValueError, "unsuccessful"):
            MODULE.parse_h2load_log("0\t500\t100\n")

    def test_simple_command_is_bound_to_artifact(self):
        artifact = pathlib.Path("/tmp/admitted-simple-web")
        self.assertTrue(MODULE.command_uses_artifact("/tmp/admitted-simple-web --port 8080", artifact))
        self.assertFalse(MODULE.command_uses_artifact("/tmp/other-server --port 8080", artifact))

    def test_fake_targets_have_exact_payload_identity(self):
        class Handler(BaseHTTPRequestHandler):
            def do_GET(self):
                body = b"same-production-payload"
                self.send_response(200)
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)

            def log_message(self, _format, *_args):
                pass

        servers = [ThreadingHTTPServer(("127.0.0.1", 0), Handler) for _ in range(2)]
        threads = [threading.Thread(target=server.serve_forever) for server in servers]
        try:
            for thread in threads:
                thread.start()
            identities = [MODULE.fetch_identity(f"http://127.0.0.1:{server.server_port}/", 1.0, False)
                          for server in servers]
            self.assertEqual(identities[0], identities[1])
            self.assertEqual(identities[0][0], len(b"same-production-payload"))
        finally:
            for server in servers:
                server.shutdown()
                server.server_close()
            for thread in threads:
                thread.join()


if __name__ == "__main__":
    unittest.main()
