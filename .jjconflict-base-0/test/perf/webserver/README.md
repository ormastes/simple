# Webserver Performance

## Current Evidence

`http_hot_path.spl` measures parser and serializer hot-path cost inside Simple.
`async_driver_native_smoke.spl` verifies the native async driver syscall backend.
These are regression checks, not live webserver throughput results.

`static_file_server.spl` is the live Simple static-file benchmark target. It is
kept pure Simple at the call site: the server uses SFFI declarations for runtime
services and does not route through a foreign implementation or comparison
target.

The current native path serves the repo `README.md` fixture with a bounded
request limit read through `rt_env_get_i64`. That avoids the native full-server
env-derived loop-bound crash tracked in
`doc/08_tracking/bug/native_static_server_env_i64_loop_bound_2026-05-13.md`.

The request hot path uses `rt_io_tcp_drain_line` for the request line, so the
server can consume a GET request without allocating a Simple `text` value for a
line it does not inspect. `rt_io_tcp_read_line` and `rt_io_tcp_drain_line` share
the chunked TCP reader, which peeks in 1024-byte chunks and consumes only
through the newline instead of issuing byte-at-a-time reads.

## Live Static Harness

Run an environment/tool probe:

```bash
python3 test/perf/webserver/live_static_compare.py --probe
```

Build the pure Simple native static server:

```bash
src/compiler_rust/target/debug/simple native-build --runtime-bundle rust-hosted \
  --source src/lib --source test --entry-closure \
  --entry test/perf/webserver/static_file_server.spl \
  --threads 1 --timeout 30 \
  --output /tmp/simple_static_server_native_hosted_pure
```

Benchmark only the Simple server:

```bash
SIMPLE_WEBSERVER_CMD='SIMPLE_STATIC_SERVER_ADDR=127.0.0.1:18080 SIMPLE_STATIC_SERVER_FILE=README.md SIMPLE_STATIC_SERVER_REQUESTS=512 /tmp/simple_static_server_native_hosted_pure' \
SIMPLE_WEBSERVER_URL=http://127.0.0.1:18080/README.md \
python3 test/perf/webserver/live_static_compare.py --requests 384 --concurrency 16 --warmup 16
```

Smoke the interpreter path with the same Simple source:

```bash
SIMPLE_WEBSERVER_CMD='SIMPLE_STATIC_SERVER_ADDR=127.0.0.1:18080 SIMPLE_STATIC_SERVER_FILE=README.md SIMPLE_STATIC_SERVER_REQUESTS=80 src/compiler_rust/target/debug/simple run test/perf/webserver/static_file_server.spl' \
SIMPLE_WEBSERVER_URL=http://127.0.0.1:18080/README.md \
python3 test/perf/webserver/live_static_compare.py --requests 64 --concurrency 8 --warmup 8
```

The harness can still benchmark externally supplied servers when a URL is
provided, but the active SFFI production target is the pure Simple server above.
