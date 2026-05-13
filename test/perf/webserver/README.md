# Webserver Performance

## Current Evidence

`http_hot_path.spl` measures parser and serializer hot-path cost inside Simple.
`async_driver_native_smoke.spl` verifies the native async driver syscall backend.
These are useful regression checks, but they do not prove live nginx parity.

`static_file_server.spl` is a bounded live Simple static-file target for this
harness. In interpreter mode on this host, a 64 request / concurrency 8 smoke
run after request-hot-path cleanup measured:

| target | avg_us | p50_us | p99_us | req_per_s | errors |
|---|---:|---:|---:|---:|---:|
| Simple static server | 4572 | 4336 | 6729 | 1509 | 0 |
| C static baseline | 3117 | 3071 | 5590 | 2154 | 0 |

This proves the live Simple target works, but it does not prove Simple is
faster than C or nginx. A native-build attempt for `static_file_server.spl`
without `--entry-closure` spun at ~100% CPU for more than three minutes without
producing an output binary. With `--entry-closure`, the core-bootstrap lane
links quickly but stubs TCP symbols.

The rust-hosted native `static_file_server.spl` path now serves the real README
fixture after simplifying the perf target to a fixed request limit and GET-only
close-after-response loop. The fixed limit avoids a native full-server
env-derived loop-bound crash tracked in
`doc/08_tracking/bug/native_static_server_env_i64_loop_bound_2026-05-13.md`;
the GET-only loop removes per-request header draining. Current 384 request /
concurrency 16 comparison against the tiny C static baseline is stable enough
for regression tracking but still noisy for a superiority claim:

| target | avg_us | p50_us | p99_us | req_per_s | errors |
|---|---:|---:|---:|---:|---:|
| Simple native static server | 4162 | 3967 | 7674 | 3441 | 0 |
| C static baseline | 5931 | 5482 | 12087 | 2475 | 0 |

A repeat on the same host measured Simple at 2908 req/s and C at 3084 req/s.
Treat these as "native Simple is in the same range as the tiny C baseline", not
as a proof that Simple is faster than C.

`static_file_server_fixed.spl` isolates native TCP with fixed port/body and no
env/file I/O. A rust-hosted native build serves traffic successfully:

| target | avg_us | p50_us | p99_us | req_per_s | errors |
|---|---:|---:|---:|---:|---:|
| Simple fixed native TCP | 2461 | 2238 | 6126 | 2697 | 0 |
| C static baseline | 2517 | 2260 | 7125 | 2837 | 0 |

This is the first live webserver data point where native Simple is roughly on
par with the C baseline. It is not nginx parity and it is not the full static
file server path yet.

## Live Static Comparison Harness

Run an environment/tool probe:

```bash
python3 test/perf/webserver/live_static_compare.py --probe
```

Benchmark supplied live servers:

```bash
SIMPLE_WEBSERVER_URL=http://127.0.0.1:8080/index.html \
NGINX_WEBSERVER_URL=http://127.0.0.1:8081/index.html \
python3 test/perf/webserver/live_static_compare.py --requests 1024 --concurrency 64
```

Or let the harness start local commands:

```bash
SIMPLE_WEBSERVER_CMD='SIMPLE_STATIC_SERVER_ADDR=127.0.0.1:18080 SIMPLE_STATIC_SERVER_FILE=README.md bin/simple run test/perf/webserver/static_file_server.spl' \
SIMPLE_WEBSERVER_URL=http://127.0.0.1:18080/README.md \
NGINX_WEBSERVER_CMD='nginx -c /tmp/simple-nginx.conf -g "daemon off;"' \
NGINX_WEBSERVER_URL=http://127.0.0.1:8081/index.html \
python3 test/perf/webserver/live_static_compare.py
```

Compare Simple against the tiny C baseline when nginx is not available:

```bash
cc -O2 -std=c11 test/perf/webserver/static_file_server_ref.c -o /tmp/simple_static_ref
SIMPLE_WEBSERVER_CMD='SIMPLE_STATIC_SERVER_ADDR=127.0.0.1:18080 SIMPLE_STATIC_SERVER_FILE=README.md bin/simple run test/perf/webserver/static_file_server.spl' \
SIMPLE_WEBSERVER_URL=http://127.0.0.1:18080/README.md \
BASELINE_WEBSERVER_NAME=c_static \
BASELINE_WEBSERVER_CMD='C_STATIC_SERVER_PORT=18081 C_STATIC_SERVER_FILE=README.md C_STATIC_SERVER_REQUESTS=2048 /tmp/simple_static_ref' \
BASELINE_WEBSERVER_URL=http://127.0.0.1:18081/README.md \
python3 test/perf/webserver/live_static_compare.py --requests 1024 --concurrency 64
```

Build and compare the fixed native TCP smoke target:

```bash
bin/simple native-build --runtime-bundle rust-hosted --source src/lib --source test \
  --entry-closure --entry test/perf/webserver/static_file_server_fixed.spl \
  --threads 1 --timeout 20 --output /tmp/simple_static_fixed_native

SIMPLE_WEBSERVER_CMD='/tmp/simple_static_fixed_native' \
SIMPLE_WEBSERVER_URL=http://127.0.0.1:18083/ \
BASELINE_WEBSERVER_NAME=c_static \
BASELINE_WEBSERVER_CMD='C_STATIC_SERVER_PORT=18081 C_STATIC_SERVER_FILE=README.md C_STATIC_SERVER_REQUESTS=512 /tmp/simple_static_ref' \
BASELINE_WEBSERVER_URL=http://127.0.0.1:18081/README.md \
python3 test/perf/webserver/live_static_compare.py --requests 96 --concurrency 8 --warmup 8
```

If `nginx` is not installed and no nginx URL is supplied, the harness reports
`SKIP,nginx_missing,no_nginx_binary_or_url`. That is intentional: no result from
this harness should be used to claim Simple is faster than nginx unless both
servers were actually measured on the same host with the same static payload.
