# Web Server Optimizer — Research Summary (Workstream A)

**Date:** 2026-05-25  
**Researcher:** Phase 2 Research Analyst

---

## AC-1: H2 Server Multiplexing (Streams, HPACK, Flow Control, SETTINGS/GOAWAY)

### What exists

**Framing layer (W15-F scope — complete):**
- `src/lib/nogc_sync_mut/http/h2/h2_frame.spl` — Tagged union `H2Frame` covering all 10 RFC 9113 frame types (DATA, HEADERS, PRIORITY, RST_STREAM, SETTINGS, PUSH_PROMISE, PING, GOAWAY, WINDOW_UPDATE, CONTINUATION). All frame type + flag constants and error codes (H2_ERR_*) defined.
- `src/lib/nogc_sync_mut/http/h2/h2_parser.spl` — Stateless byte → H2Frame parser. Big-endian, R-bit masked. Returns nil on malformed input. **PADDED flag handling deferred** (returns nil when set).
- `src/lib/nogc_sync_mut/http/h2/h2_writer.spl` — H2Frame → [u8] serializer. All 10 frame types. Big-endian. Caller responsible for SETTINGS_MAX_FRAME_SIZE compliance.
- `src/lib/nogc_sync_mut/http/h2/h2_preface.spl` — Connection preface handling.
- Async mirror: `src/lib/nogc_async_mut/http/h2/` has identical 4 files (h2_frame, h2_parser, h2_preface, h2_writer) — same scope.

**Explicitly deferred (W16+ per in-file comments):**
- HPACK header compression — `header_block` payloads stay opaque `[u8]`
- Connection state machine and stream lifecycle
- Flow control accounting (WINDOW_UPDATE tracking)
- PADDED flag handling for DATA/HEADERS/PUSH_PROMISE
- PRIORITY-in-HEADERS sub-payload (5-byte block)
- SETTINGS_MAX_FRAME_SIZE enforcement

### Gap summary for AC-1
**Missing:** HPACK encoder/decoder, H2 connection state machine (stream open/close/reset lifecycle), flow control credit accounting (per-stream + connection window), SETTINGS exchange/ACK logic, GOAWAY send/receive integration into server loop. The wire-level framing is done but the protocol engine above it is absent.

---

## AC-2: H3 Server over QUIC/UDP (QUIC Transport, Connection IDs, Loss Detection, Congestion)

### What exists

**Frame layer (complete):**
- `src/lib/nogc_sync_mut/http/h3/h3_frame.spl` — RFC 9114 §7.2 frame types with variable-length integer encoding (RFC 9000 §16). DATA, HEADERS, CANCEL_PUSH, SETTINGS, PUSH_PROMISE, GOAWAY, MAX_PUSH_ID.
- `src/lib/nogc_sync_mut/http/h3/h3_conn.spl` — Connection state machine (Idle → Open → Closing → Draining → Closed per RFC 9114 §5). State transitions only — no actual QUIC transport.
- `src/lib/nogc_sync_mut/http/h3/h3_stream.spl` — Stream kind enum (Bidi/UniControl/UniPush/UniQpackEncoder/UniQpackDecoder), stream state machine, QUIC stream-id helpers (RFC 9000 §2.1).
- `src/lib/nogc_sync_mut/http/h3/qpack_encoder.spl` — QPACK static-table-only encoding (RFC 9204 §4.5). Prefixed integers, Huffman, indexed/literal representations. **No dynamic table.**
- `src/lib/nogc_sync_mut/http/h3/qpack_decoder.spl` — QPACK static-table-only decoding. Same scope constraint.
- `src/lib/nogc_sync_mut/http/h3/qpack_static.spl` — Static table.
- Async mirror: `src/lib/nogc_async_mut/http/h3/` has only `h3_frame.spl` + `qpack_static.spl` (subset).

**UDP transport exists:**
- `src/lib/nogc_async_mut/io/udp.spl` — `AsyncUdpSocket` backed by sync `UdpSocket`. Future-returning `send_to`, `recv_from`, `connect`. This is a ready-future facade (no epoll/io_uring integration — wraps sync syscalls).

**No QUIC transport anywhere:**  
- Grep for `rt_quic`, `quic_send`, `quic_recv` across runtime C/H files returns only quickjs.h hits (JavaScript engine, unrelated).
- All H3 files explicitly document "No QUIC transport — frame layer only."
- H3 conn/stream deferred list includes: "QUIC transport integration (RFC 9000)", "Flow control accounting (RFC 9000 §4)", "Actual QUIC transport send/receive".
- QPACK: dynamic table deferred in both encoder and decoder.

### Gap summary for AC-2
**Missing (all of QUIC):** Packet format (Initial/Handshake/1-RTT/Retry), connection IDs, crypto bootstrap (QUIC-TLS), packet number spaces, loss detection (RFC 9002), congestion control (Reno/CUBIC per RFC 9002), stream multiplexing over UDP, flow control. Additionally: QPACK dynamic table, H3 request/response engine wired to actual transport. This AC requires building QUIC from scratch or integrating a library (e.g., quinn/quiche via SFFI).

---

## AC-3: Static File Performance (sendfile, Pre-compressed Cache, mmap, ETag, Range)

### What exists

**`src/lib/nogc_async_mut/http_server/static_file.spl` (most complete AC):**
- `StaticFileHandler` — serves from configured root, path traversal protection, directory index.
- `IoDriver.submit_sendfile()` — zero-copy sendfile path wired in (`use_sendfile` branch in `ConnectionAction`). Large files (> 64 KiB) use sendfile; small files go through in-memory compression cache.
- `StaticCompressionCache` — LRU cache of pre-compressed payloads keyed by `(path, encoding)`. Stores gzip/brotli/zstd-compressed bytes. Cache capacity configurable.
- `Last-Modified` / `If-Modified-Since` — present per feature doc.
- MIME type detection from extension.

**`src/lib/nogc_async_mut/http_server/http_capability_router.spl`:**
- `HttpBackendCaps` — struct with `supports_sendfile: bool`, `supports_zero_copy: bool`.
- `http_route_static_file(caps, has_file_body)` — dispatches to sendfile / portable-read / in-memory body based on backend caps.
- Three capability constructors: `portable`, `sendfile`, `zero_copy`.

**`src/lib/nogc_async_mut/http_server/connection.spl`:**
- `ConnectionAction` — `use_sendfile: bool`, `use_portable_read: bool` fields drive worker I/O path.

**Missing from static_file.spl:**
- **ETag / If-None-Match** — not present (grep returns no output).
- **Range / 206 Partial Content / Content-Range** — not present (grep returns no output).
- **mmap** — not mentioned in static_file.spl; sendfile replaces it for large files but explicit mmap is absent.
- nginx benchmark harness — not present.

### Gap summary for AC-3
Sendfile zero-copy and pre-compression cache are implemented. Last-Modified/If-Modified-Since is present. **Missing:** ETag generation (hash-based), If-None-Match 304 path, Range header parsing + 206 Partial Content response, nginx benchmark comparison script.

---

## AC-4: Unified Server — ALPN Negotiation Dispatching to H1/H2/H3

### What exists

**TLS stack (`src/lib/nogc_async_mut/io/`):**
- `tls.spl` — `AsyncTlsStream`, `AsyncTlsListener`. TLS 1.2 record layer, AES-GCM. Backed by `perform_server_handshake`.
- `tls_handshake.spl` — `perform_server_handshake`. Parses ClientHello (version, random, session_id, cipher_suites, extensions). Extensions field is **sliced as raw bytes** — the extension list is captured but no extension types are dispatched/parsed beyond cipher negotiation. **ALPN extension (type 0x0010) is NOT parsed or acted upon.**
- Cipher negotiation: only `TLS_RSA_WITH_AES_128_GCM_SHA256` is supported.

**HTTP server (`src/lib/nogc_async_mut/http_server/`):**
- `worker.spl` — imports `AsyncTlsListener`, `AsyncTlsStream`, `TlsConfig`. Grep for `h2`, `h3`, `alpn`, `upgrade`, `protocol_version` returns **no output** — worker has no H2/H3 dispatch logic.
- `connection.spl` — grep for protocol upgrade/h2/h3 returns **no output**. Connection state machine handles H1 only.
- `server.spl` — master process, nginx-style worker lifecycle. No protocol dispatch.

### Gap summary for AC-4
**Missing entirely:** ALPN extension parsing in TLS handshake (must detect `h2` / `h3` from ClientHello extensions), post-handshake protocol dispatch in worker (branch to H1/H2/H3 connection handler based on negotiated protocol), H2 connection handler (pending AC-1 engine), H3 connection handler (pending AC-2 QUIC). The TLS layer needs extension-aware parsing before ALPN can work.

---

## AC-5: All Server Specs Pass

### What exists
- Test infrastructure: `test/` directory, spipe framework, `bin/simple test` runner.
- No web-server-optimizer-specific spec files were found in this research pass.

### Gap summary for AC-5
Specs need to be written for all new ACs. Existing server tests (if any) cover H1 only.

---

## Architectural Constraints

| Concern | Finding |
|---|---|
| Event loop UDP support | `AsyncUdpSocket` exists but is a sync-wrapper facade — no io_uring/epoll integration for UDP datagrams. QUIC would need a real async UDP path. |
| TLS cipher agility | Only AES-128-GCM-SHA256 + RSA. No TLS 1.3. QUIC-TLS requires TLS 1.3 — needs new cipher + key schedule work. |
| HPACK | Completely absent. H2 is blocked on this. Consider reusing QPACK encoder/decoder structure (same prefixed-int + Huffman base). |
| QPACK dynamic table | Absent in both encoder and decoder. Static-table-only is functional for small header sets but will regress on large/dynamic workloads. |
| sendfile integration | `submit_sendfile` is called but actual runtime extern (`rt_sendfile` or equivalent) needs to be confirmed present in the runtime. `net_perf.spl` is present but returned no sendfile grep hits. |
| mmap | Not used. For very large static assets, mmap+write may outperform sendfile in some scenarios, but sendfile is sufficient for nginx parity. |

---

## Reusable Code Paths

| File | Reusable For |
|---|---|
| `src/lib/nogc_sync_mut/http/h2/h2_frame.spl` | H2 connection engine — frame types/constants already defined |
| `src/lib/nogc_sync_mut/http/h2/h2_parser.spl` + `h2_writer.spl` | H2 engine I/O layer |
| `src/lib/nogc_sync_mut/http/h3/qpack_encoder.spl` + `qpack_decoder.spl` | HPACK bootstrap (same RFC 7541 base) |
| `src/lib/nogc_sync_mut/http/h3/h3_frame.spl` | H3 framing — varint, all frame types ready |
| `src/lib/nogc_sync_mut/http/h3/h3_conn.spl` + `h3_stream.spl` | H3 state machine scaffold |
| `src/lib/nogc_async_mut/io/udp.spl` | QUIC UDP send/recv (needs async integration upgrade) |
| `src/lib/nogc_async_mut/io/tls_handshake.spl:301` | `parse_client_hello_payload` — extend to parse extension type 0x0010 for ALPN |
| `src/lib/nogc_async_mut/http_server/static_file.spl` | Static file serving — add ETag + Range on top |
| `src/lib/nogc_async_mut/http_server/http_capability_router.spl` | Backend capability dispatch — already sendfile-aware |

---

## Open Questions

1. **QUIC strategy:** Build QUIC in pure Simple vs. SFFI-bind quinn/quiche? Given the full absence of QUIC transport, SFFI binding (via `quiche` C API) is far more feasible within a single workstream. Pure-Simple QUIC is a multi-month effort.
2. **HPACK:** Build from scratch or port QPACK encoder/decoder (same integer/Huffman base)? The QPACK code reuse path looks viable.
3. **sendfile runtime:** Confirm `rt_sendfile` or equivalent extern exists in `src/runtime/`. `net_perf.spl` grep returned nothing — verify `submit_sendfile` is wired to an actual syscall.
4. **TLS 1.3:** Required for QUIC-TLS (RFC 9001). Currently only TLS 1.2 is implemented. This is a significant prerequisite for AC-2.
5. **nginx benchmark:** What baseline nginx version and config to benchmark against? Which metrics matter (RPS, p99 latency, large-file throughput)?
6. **H2 in worker:** Does AC-1 engine land in `worker.spl` or as a separate connection handler class? The current worker is tightly coupled to H1 parser flow.
