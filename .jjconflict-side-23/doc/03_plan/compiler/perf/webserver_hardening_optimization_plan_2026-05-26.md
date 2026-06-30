# Webserver Hardening And Optimization Plan - 2026-05-26

## Purpose

Consolidate Simple HTTP server hardening, async I/O modernization, sendfile,
QUIC/H3, HPACK, and nginx-comparison benchmark work into one webserver track.

## Source Plans

- `doc/05_design/async_io_nginx_perf_optimization.md`
- `doc/05_design/simple_web_server_lib_api.md`
- `doc/05_design/simple_web_server_split.md`
- `doc/05_design/simple_web_server_example.md`
- `doc/05_design/net_http_sendfile_routing.md`
- `doc/03_plan/sys_test/net_http_sendfile_routing.md`
- `doc/01_research/lib/networking/net_http_sendfile_routing.md`
- `test/05_perf/web_server_nginx_compare/`
- `src/lib/nogc_async_mut/http/h2/hpack_huffman.spl`
- `src/lib/nogc_async_mut/quic/`

## Scope

- Harden HTTP parsing and routing:
  - bounded request line/header/body sizes
  - timeout and keep-alive limits
  - bad-request handling without panics
  - path traversal refusal for static files
  - header canonicalization and duplicate policy.
- Optimize static-file serving:
  - route static file responses to sendfile when backend supports it
  - portable-read fallback remains explicit and measurable
  - no body-copy path for sendfile-capable static responses.
- Modernize async server runtime:
  - thread-per-core server runtime for I/O-bound workloads
  - per-worker event loop and arena
  - SO_REUSEPORT where supported
  - bounded logging/backpressure on hot paths.
- Continue protocol work:
  - HPACK Huffman correctness and decode/encode coverage
  - QUIC/H3 wrapper coverage without unresolved native symbols in pure tests
  - clear provider boundary for quiche/SFFI runtime calls.
- Benchmark against nginx with reproducible workload generation and report
  formatting.

## Crash-Safe Execution Rules

- Webserver load tests must not run in parallel with QEMU, board serial capture,
  full bootstrap, or DB/filesystem benchmarks.
- Use local loopback by default; external network tests need explicit plan
  notes.
- Bound load tests by duration, concurrency, and generated fixture size.
- Record CPU, memory, open file limit, port, tool (`wrk` or `ab`), and command.

## Work Queue

1. Add hardening specs for parser limits, path traversal, timeout policy, and
   static-file response routing.
2. Stabilize sendfile routing:
   - `portable-read` when unavailable
   - `sendfile` only when supported
   - zero-copy without sendfile does not incorrectly route to sendfile.
3. Make nginx comparison harness deterministic:
   - fixture generator
   - simple/nginx labels
   - p99 latency, RPS, throughput, and failure count
   - report under `doc/10_metrics/`.
4. Keep QUIC/H3 as provider-bound:
   - pure wrapper tests do not require native quiche symbols
   - runtime provider availability is explicit.
5. Add optimization-plugin follow-up facts for web hot paths:
   - header scan
   - route lookup
   - static-file copy/sendfile decision
   - HPACK bit loops.

## Verification Gates

- Parser and routing specs pass before load tests.
- Load-test reports include nginx baseline and Simple result from the same
  machine/run window.
- Static-file fast path shows which backend was used: `sendfile`,
  `portable-read`, or explicit unsupported-provider refusal.
- No webserver hardening claim may rely on unbounded request size, unbounded
  connection lifetime, or unbounded logging.
