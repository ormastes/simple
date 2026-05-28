# HTTP Server Benchmark Report — 2026-05-28

## Summary

Native-compiled Simple HTTP server benchmarked against nginx for static file serving.
Simple achieves **1.5–2x nginx throughput** at equal worker count.

## Environment

- CPU: 32-core (AMD/Intel)
- OS: Linux 6.8.0-117-generic
- wrk: 4 threads, 10s duration
- File: `/tmp/simple_bench_data/hello.txt` (13 bytes, "Hello, World!")
- Simple binary: `build/bench_raw_tcp_static` (29 KB), native LLVM codegen
- nginx: system package, sendfile on, tcp_nodelay on, reuseport, access_log off

## Static File Serving (pre-cached vs sendfile)

| Config | Simple RPS | nginx RPS | Ratio |
|--------|-----------|-----------|-------|
| 1 worker, 100 conn | 49,904 | 25,245 | **1.98x** |
| 4 workers, 400 conn | 136,486 | 89,145 | **1.53x** |
| 32 workers (nginx auto), 400 conn | — | 137,982 | client-limited |

Simple 4 workers matches nginx 32 workers (~137K RPS) — wrk is the bottleneck.

## Hardcoded Response (from prior session)

| Config | Simple RPS | nginx RPS | Ratio |
|--------|-----------|-----------|-------|
| 1 worker, 100 conn | 56,759 | 51,077 (inline) | **1.11x** |
| 4 workers, 100 conn | 98,488 | 89,460 | **1.10x** |
| 4 workers, 400 conn | 127,164 | — | peak |

## UDP Throughput Sink (native, single thread)

| Metric | 1 sender | 4 senders |
|--------|----------|-----------|
| Client send rate | 130,709 pkt/s | 192,577 pkt/s |
| Server receive rate (steady) | ~16,000–24,000 pkt/s | ~27,000–33,000 pkt/s |
| Total received | 92,800 pkts (5s) | 295,747 pkts (10s) |
| Packet size | 64 bytes | 64 bytes |

Server: epoll edge-triggered, nonblocking recvfrom, batch 64.
Bottleneck: single-thread recvfrom + epoll overhead. SO_REUSEPORT multi-process would scale linearly (~120K+ pkt/s with 4 workers).

## Cross-Platform Event Backends (code-verified)

| Backend | File | Lines | Status |
|---------|------|-------|--------|
| epoll (Linux) | `src/runtime/platform/async_linux_epoll.c` | 957 | **Real** — epoll_create1, epoll_ctl, epoll_wait |
| io_uring (Linux) | `src/runtime/platform/async_linux_uring.c` | 738 | **Real** — io_uring_submit, io_uring_prep_* |
| kqueue (FreeBSD) | `src/runtime/platform/async_freebsd.c` | 761 | **Real** — kqueue, kevent + kernel AIO |
| kqueue (macOS) | `src/runtime/platform/async_macos.c` | 827 | **Real** — kqueue, kevent |
| IOCP (Windows) | `src/runtime/platform/async_windows.c` | 926 | **Real** — CreateIoCompletionPort, GetQueuedCompletionStatusEx |
| event_ports (Solaris) | stubs in runtime_native.c | — | **Stub** — returns -1 |

Dispatch: `src/runtime/platform/async_driver.c` (311 LOC) — vtable dispatch, `#ifdef` selects backend at compile time.
All edge-triggered where supported. io_uring available as alternative to epoll on Linux (M4+).

## Architecture

- **Simple**: epoll edge-triggered, SO_REUSEPORT, nonblocking accept loop (batch 64), pre-cached file content in memory, single write per request. Pure C runtime externs + Simple LLVM codegen.
- **nginx**: epoll, SO_REUSEPORT, sendfile (kernel zero-copy), worker_connections 10K.

## What Was Benchmarked

- Native LLVM-compiled TCP server reading file from disk at startup
- HTTP/1.1 keep-alive with Connection: keep-alive
- Single small static file (13 bytes)
- SO_REUSEPORT multi-process scaling

## What Was NOT Benchmarked

- HTTP request URL parsing (all requests serve same file)
- Large file serving (sendfile advantage)
- Dynamic content / template rendering
- HTTPS/TLS termination (delegates to Rust rustls by design — not a pure Simple path)
- HTTP/2 multiplexing (H2 exists in pure Simple, not benchmarked natively)
- HTTP/3 / QUIC (exists in pure Simple, not benchmarked natively)
- Embedded HTTP server (`EmbeddedHttpServer` class compiles natively but lacks `serve_forever()`/`create()` — class has route registration + request handling but no socket listen loop yet; code gap, not build issue)
- Multi-file download / range requests / compression
- Cross-platform events: 5/6 backends code-verified (epoll, io_uring, kqueue×2, IOCP), only epoll benchmarked on this machine; event_ports is stub
- UDP multi-process scaling (SO_REUSEPORT — single-thread only so far)

## Design Decisions

- **TLS/HTTPS delegates to Rust rustls** — not a pure Simple path. This is a deliberate performance/security trade-off: TLS implementations require constant-time operations, side-channel resistance, and audit rigor that make a pure Simple reimplementation impractical. All HTTP/2, HTTP/3, QUIC framing above TLS is pure Simple.

## Known Bugs

- **`text.len()` native codegen**: Returns garbage (0x1FFFFFFFFFFFFFFF) instead of actual length.
  Workaround: `extern fn rt_string_len(s: text) -> i64`. See `doc/08_tracking/bug/native_codegen_text_len_garbage_2026-05-28.md`.

## Feature Verification

| Feature | Status | Verified | Location |
|---------|--------|----------|----------|
| TCP static file serving | Pure Simple | **Benchmarked** (1.5–2x nginx) | `bench_raw_tcp_static.spl` |
| UDP socket | Pure Simple | **Benchmarked** (~30K pkt/s) | `src/lib/nogc_sync_mut/io/udp.spl` |
| HTTP/2 framing | Pure Simple | Source-only (tests fail in interpreter) | `src/lib/nogc_async_mut/http/h2/` (~6 files) |
| HTTP/3 framing | Pure Simple | Source-only, runtime unverified | `src/lib/nogc_async_mut/http/h3/` (~4 files) |
| QUIC transport | Pure Simple | Source-only, runtime unverified | `src/lib/nogc_async_mut/io/quic/` (~3 files) |
| HPACK + Huffman | Pure Simple | Source-only, runtime unverified | `h2_hpack.spl`, `hpack_huffman.spl` |
| QPACK encode/decode | Pure Simple | Source-only, runtime unverified | `qpack_encoder.spl`, `qpack_decoder.spl` |
| TLS handshake/record | Delegates to Rust rustls | N/A (by design) | `src/lib/nogc_sync_mut/tls/tls_sffi.spl` |
| Cross-platform events | Pure Simple dispatch, C backends | 5/6 code-verified, epoll benchmarked | epoll/io_uring/kqueue(BSD+Mac)/IOCP/poll |
| Embedded HTTP server | Pure Simple | Blocked (no serve loop) | `http_server/embedded.spl` |
| Static file serving | Pure Simple | Source-only | `http_server/static_file.spl` |
| Response cache (LRU) | Pure Simple | Source-only | `http_server/response_cache.spl` |
| Range requests | Pure Simple | Source-only | `http_server/range.spl` |
| Multipart/ZIP/TAR | Pure Simple | Source-only | `http_server/multipart_response.spl` |

## Files

- TCP static benchmark: `test/perf/bench/http_server/bench_raw_tcp_static.spl`
- UDP sink benchmark: `test/perf/bench/http_server/bench_udp_echo.spl`
- C runtime additions: `src/runtime/runtime_native.c` (`rt_file_read_all_text`)
- nginx config: `test/perf/bench/http_server/nginx_bench.conf`
- Bug report: `doc/08_tracking/bug/native_codegen_text_len_garbage_2026-05-28.md`
