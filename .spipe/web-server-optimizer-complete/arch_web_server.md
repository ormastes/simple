# Web Server Optimizer — Architecture (Workstream A)

**Feature:** web-server-optimizer-complete  
**Date:** 2026-05-25  
**Scope:** All four ACs: H2 engine (AC-1), QUIC/H3 SFFI bridge (AC-2), static file perf (AC-3), unified ALPN dispatch (AC-4).

---

## Guiding constraints

- All new code in `.spl`. No Python/Bash.
- No inheritance. Composition, traits, mixins only. Generics use `<>`.
- Library code (not userland service) — MDSOC+ ECS applies only to apps/services. Protocol engines here are plain data structures + functions.
- New async files land in `src/lib/nogc_async_mut/`. Sync primitives shared with existing `src/lib/nogc_sync_mut/` via import.
- TLS split: H2 path uses the existing `tls_handshake.spl` (TLS 1.2 + ALPN extension added in AC-4). H3 path delegates handshake entirely to quiche (quiche embeds BoringSSL with TLS 1.3). The SimpleOS TLS stack does NOT need TLS 1.3 for this workstream.

---

## Module dependency order

```
hpack_primitives  (new, extracted RFC 7541 core)
    └── h2_hpack         (new, AC-1 — HPACK using primitives)
        └── h2_stream    (new, AC-1 — stream lifecycle + per-stream flow control)
            └── h2_connection  (new, AC-1 — connection SM, SETTINGS, GOAWAY)
                └── h2_server  (new, AC-1 — server-side mux engine)

quic_sffi          (new, AC-2 — quiche C API contract)
    └── h3_server  (new, AC-2 — H3 over quiche QUIC)

static_file.spl    (modified, AC-3 — ETag + Range on top of existing)

tls_handshake.spl  (modified, AC-4 — parse ALPN extension 0x0010)
protocol_handler   (new, AC-4 — trait + H1/H2/H3 impls + dispatch table)
worker.spl         (modified, AC-4 — ALPN result → ProtocolHandler dispatch)
```

---

## AC-1: H2 Server Engine

### 1a. `src/lib/nogc_async_mut/http/hpack_primitives.spl` (new)

**Purpose:** Shared RFC 7541 §5 encoding primitives. Both `h2_hpack.spl` and the existing QPACK encoder/decoder should import this. Currently those primitives are duplicated inside the QPACK files; this module is the canonical home.

**Key functions:**
```
fn hpack_encode_int(prefix_bits: u8, value: u32) -> [u8]
fn hpack_decode_int(buf: [u8], offset: u32, prefix_bits: u8) -> (u32, u32)  // (value, bytes_consumed)
fn hpack_encode_string_raw(s: text) -> [u8]       // H=0 literal (no Huffman)
fn hpack_encode_string_huffman(s: text) -> [u8]   // H=1 Huffman
fn hpack_decode_string(buf: [u8], offset: u32) -> (text, u32)
```

**Depends on:** nothing in this codebase (pure RFC 7541 §5 arithmetic).  
**Note:** `qpack_encoder.spl` and `qpack_decoder.spl` may be migrated to import this in a follow-up; new code uses it directly.

---

### 1b. `src/lib/nogc_async_mut/http/h2/h2_hpack.spl` (new)

**Purpose:** HPACK encoder/decoder (RFC 7541). Static table only in this workstream (mirrors current QPACK scope). Dynamic table management deferred.

**Key types:**
```
struct HpackTable {
  static_entries: [HpackEntry]   // RFC 7541 Appendix A, 61 entries — constant
}

struct HpackEntry {
  name:  text
  value: text
}

struct HpackEncodeResult {
  bytes: [u8]
}

struct HpackDecodeResult {
  headers: [(text, text)]
  bytes_consumed: u32
}
```

**Key functions:**
```
fn hpack_encode(headers: [(text, text)], table: HpackTable) -> HpackEncodeResult
fn hpack_decode(buf: [u8], table: HpackTable) -> Result<HpackDecodeResult, text>
fn hpack_static_table() -> HpackTable
```

**State invariants:** Static table is immutable. Dynamic table size = 0 (deferred).  
**Depends on:** `hpack_primitives.spl`, `src/lib/nogc_async_mut/http/h2/h2_frame.spl` (H2_HPACK_* constants).

---

### 1c. `src/lib/nogc_async_mut/http/h2/h2_stream.spl` (new)

**Purpose:** Per-stream lifecycle state machine and flow control credit accounting (RFC 9113 §5 + §6.9).

**Stream states (RFC 9113 §5.1):**
```
enum H2StreamState {
  Idle
  Open
  HalfClosedLocal
  HalfClosedRemote
  Closed
  ReservedLocal
  ReservedRemote
}
```

**Key types:**
```
struct H2Stream {
  id:               u32
  state:            H2StreamState
  send_window:      i32           // per-stream send credit (may go negative during RST)
  recv_window:      i32           // per-stream receive credit
  recv_window_init: i32           // initial value for reset
  header_block_buf: [u8]          // accumulates CONTINUATION frames
  headers:          [(text, text)] // decoded after END_HEADERS
  weight:           u8
  dependency:       u32
}
```

**Key functions:**
```
fn h2_stream_new(id: u32, send_window_init: i32, recv_window_init: i32) -> H2Stream
fn h2_stream_apply_frame(stream: H2Stream, frame: H2Frame) -> Result<H2Stream, H2StreamError>
fn h2_stream_consume_send_credit(stream: H2Stream, n: i32) -> Result<H2Stream, H2StreamError>
fn h2_stream_grant_recv_credit(stream: H2Stream, increment: u32) -> H2Stream
fn h2_stream_is_writable(stream: H2Stream) -> bool
fn h2_stream_is_closed(stream: H2Stream) -> bool

enum H2StreamError {
  InvalidTransition(H2StreamState, text)  // (current_state, attempted_action)
  FlowControlViolation
  StreamClosed
}
```

**State invariants:**
- `send_window >= 0` before DATA frames are sent; caller must check `is_writable`.
- CONTINUATION frames only valid when `header_block_buf` is non-empty (open HEADERS sequence).

**Depends on:** `h2_frame.spl`, `h2_hpack.spl`.

---

### 1d. `src/lib/nogc_async_mut/http/h2/h2_connection.spl` (new)

**Purpose:** H2 connection state machine: SETTINGS exchange, GOAWAY, connection-level flow control, stream registry. Multiplexes frames to `H2Stream` instances.

**Key types:**
```
struct H2Settings {
  header_table_size:      u32   // default 4096
  enable_push:            u32   // 0 or 1
  max_concurrent_streams: u32   // default unlimited (u32::MAX)
  initial_window_size:    u32   // default 65535
  max_frame_size:         u32   // default 16384, must be 16384..16777215
  max_header_list_size:   u32   // default unlimited
}

struct H2Connection {
  state:               H2ConnState
  local_settings:      H2Settings
  remote_settings:     H2Settings
  pending_settings:    Option<H2Settings>   // awaiting SETTINGS ACK
  conn_send_window:    i32                  // connection-level send credit
  conn_recv_window:    i32                  // connection-level receive credit
  streams:             Map<u32, H2Stream>   // stream_id → H2Stream
  next_stream_id:      u32                  // server-initiated push streams (even IDs)
  last_client_stream:  u32                  // highest client stream seen (for GOAWAY)
  hpack_table:         HpackTable
}

enum H2ConnState {
  Preface       // awaiting client preface
  Open          // active
  GoingAway     // GOAWAY sent, draining
  Closed
}
```

**Key functions:**
```
fn h2_conn_new(local: H2Settings) -> H2Connection
fn h2_conn_receive_frame(conn: H2Connection, frame: H2Frame) -> Result<(H2Connection, H2ConnEvent), H2ConnError>
fn h2_conn_send_settings(conn: H2Connection) -> ([u8], H2Connection)
fn h2_conn_ack_settings(conn: H2Connection) -> ([u8], H2Connection)
fn h2_conn_send_goaway(conn: H2Connection, error_code: u32, debug: text) -> ([u8], H2Connection)
fn h2_conn_send_window_update(conn: H2Connection, stream_id: u32, increment: u32) -> ([u8], H2Connection)
fn h2_conn_get_stream(conn: H2Connection, id: u32) -> Option<H2Stream>

enum H2ConnEvent {
  None
  RequestReady(u32, [(text, text)])   // (stream_id, headers) — END_HEADERS received
  DataChunk(u32, [u8], bool)          // (stream_id, data, end_stream)
  StreamReset(u32, u32)               // (stream_id, error_code)
  PingAck([u8])
  SettingsAcked
  GoAwayReceived(u32, u32)            // (last_stream_id, error_code)
}
```

**Data flow:**
1. Caller feeds raw TLS bytes → `h2_parser.spl` → `H2Frame`.
2. `h2_conn_receive_frame` dispatches frame to the appropriate stream or connection handler.
3. Returns `H2ConnEvent` telling the server layer what happened.
4. Server layer acts on `RequestReady` (dispatch to router), `DataChunk` (forward body), etc.

**State invariants:**
- `conn_send_window` never goes below 0 before a DATA send (checked via `h2_stream_is_writable`).
- SETTINGS ACK must be sent before processing any further frames after SETTINGS receipt.
- Stream IDs from client are odd; server-push IDs are even.

**Depends on:** `h2_stream.spl`, `h2_frame.spl`, `h2_parser.spl`, `h2_writer.spl`, `h2_preface.spl`, `h2_hpack.spl`.

---

### 1e. `src/lib/nogc_async_mut/http/h2/h2_server.spl` (new)

**Purpose:** Server-side H2 multiplexing engine. Reads frames from an `AsyncTlsStream`, drives `H2Connection`, and feeds `RequestReady` events to the existing HTTP router.

**Key types:**
```
struct H2ServerConn {
  conn:    H2Connection
  stream:  AsyncTlsStream
  router:  HttpRouter        // existing router from http_server/
}
```

**Key functions:**
```
fn h2_server_conn_new(tls: AsyncTlsStream, settings: H2Settings, router: HttpRouter) -> H2ServerConn
fn h2_server_conn_run(sc: H2ServerConn) -> Future<Result<(), text>>
  // Read loop: parse frame → h2_conn_receive_frame → dispatch event:
  //   RequestReady → router.handle(headers) → write response frames back
  //   DataChunk    → accumulate body
  //   StreamReset  → discard stream state
  //   GoAwayReceived → drain + close
fn h2_server_send_response(sc: H2ServerConn, stream_id: u32, status: u32, headers: [(text, text)], body: [u8]) -> Future<Result<(), text>>
```

**Data flow:**
```
AsyncTlsStream.read()
  → h2_parser.parse_frame(bytes)
  → h2_conn_receive_frame(conn, frame) → H2ConnEvent
  → match event:
      RequestReady(sid, hdrs) → HttpRouter.route(hdrs) → Response
                              → h2_writer.serialize(HEADERS frame + DATA frame)
                              → AsyncTlsStream.write(bytes)
      DataChunk               → body accumulation buffer
      StreamReset / GoAway    → cleanup
```

**Depends on:** `h2_connection.spl`, `h2_frame.spl`, `h2_parser.spl`, `h2_writer.spl`, `src/lib/nogc_async_mut/io/tls.spl`, `src/lib/nogc_async_mut/http_server/` router types.

---

## AC-2: QUIC Transport + H3 Server

### Design decision: SFFI binding to quiche

Building a full QUIC transport stack in pure Simple (packet format, connection IDs, QUIC-TLS with TLS 1.3, loss detection, congestion control) is a multi-month effort and out of scope for this workstream. The SimpleOS TLS stack only implements TLS 1.2; TLS 1.3 (required by RFC 9001 §4) is absent. **Decision: SFFI-bind cloudflare/quiche (C API), which embeds BoringSSL with TLS 1.3.** Simple manages the H3 application layer above it.

**Async UDP concern:** `AsyncUdpSocket` is a sync-facade (no epoll/io_uring integration). quiche's event model uses datagram batch read/write. For this workstream, quiche runs in a dedicated worker thread using the existing sync `UdpSocket`. Upgrading `AsyncUdpSocket` to true io_uring integration is a follow-up filed as a separate TODO.

---

### 2a. `src/lib/nogc_async_mut/quic/quic_sffi.spl` (new)

**Purpose:** SFFI contract for the quiche C API. Defines externs and wrapper types; zero business logic.

**SFFI externs (mapped to quiche C API):**
```
extern fn rt_quiche_config_new(version: u32) -> ptr
extern fn rt_quiche_config_free(cfg: ptr)
extern fn rt_quiche_config_set_application_protos(cfg: ptr, protos: [u8]) -> i32
extern fn rt_quiche_config_set_max_idle_timeout(cfg: ptr, ms: u64)
extern fn rt_quiche_config_set_initial_max_data(cfg: ptr, v: u64)
extern fn rt_quiche_config_set_initial_max_stream_data_bidi_remote(cfg: ptr, v: u64)
extern fn rt_quiche_config_set_initial_max_streams_bidi(cfg: ptr, v: u64)
extern fn rt_quiche_config_load_cert_chain_from_pem_file(cfg: ptr, path: text) -> i32
extern fn rt_quiche_config_load_priv_key_from_pem_file(cfg: ptr, path: text) -> i32

extern fn rt_quiche_accept(scid: [u8], odcid: [u8], local: ptr, peer: ptr, cfg: ptr) -> ptr
extern fn rt_quiche_conn_recv(conn: ptr, buf: [u8], info: ptr) -> i64
extern fn rt_quiche_conn_send(conn: ptr, out: [u8], info: ptr) -> i64
extern fn rt_quiche_conn_is_established(conn: ptr) -> bool
extern fn rt_quiche_conn_is_closed(conn: ptr) -> bool
extern fn rt_quiche_conn_stream_recv(conn: ptr, id: u64, out: [u8], fin: ptr) -> i64
extern fn rt_quiche_conn_stream_send(conn: ptr, id: u64, buf: [u8], fin: bool) -> i64
extern fn rt_quiche_conn_readable(conn: ptr) -> ptr     // returns quiche_stream_iter
extern fn rt_quiche_stream_iter_next(iter: ptr, id: ptr) -> bool
extern fn rt_quiche_stream_iter_free(iter: ptr)
extern fn rt_quiche_conn_close(conn: ptr, app: bool, err: u64, reason: [u8]) -> i32
extern fn rt_quiche_conn_free(conn: ptr)
```

**Wrapper types:**
```
struct QuicConfig {
  raw: ptr   // quiche_config*
}

struct QuicConn {
  raw: ptr   // quiche_conn*
}

struct QuicRecvInfo {
  from: [u8; 28]   // sockaddr_storage (IPv4 or IPv6)
  to:   [u8; 28]
}

struct QuicSendInfo {
  to:   [u8; 28]
  from: [u8; 28]
  at:   u64        // quiche_send_info.at (timespec nanoseconds)
}
```

**Key wrapper functions:**
```
fn quic_config_new_server(cert_pem: text, key_pem: text, alpn: text) -> Result<QuicConfig, text>
fn quic_conn_accept(scid: [u8], odcid: [u8], local_addr: [u8], peer_addr: [u8], cfg: QuicConfig) -> Result<QuicConn, text>
fn quic_conn_recv(conn: QuicConn, dgram: [u8], info: QuicRecvInfo) -> Result<i64, text>
fn quic_conn_send(conn: QuicConn, out_buf: [u8]) -> Result<(i64, QuicSendInfo), text>
fn quic_conn_stream_recv(conn: QuicConn, id: u64, out: [u8]) -> Result<(i64, bool), text>  // (n, fin)
fn quic_conn_stream_send(conn: QuicConn, id: u64, data: [u8], fin: bool) -> Result<i64, text>
fn quic_conn_readable_streams(conn: QuicConn) -> [u64]
fn quic_conn_close(conn: QuicConn) -> Result<(), text>
```

**Depends on:** SFFI runtime. C side: `quiche.h` + `libquiche.a` linked via `build.spl` or `Cargo.toml` for the Rust seed layer.

---

### 2b. `src/lib/nogc_async_mut/quic/h3_server.spl` (new)

**Purpose:** H3 application layer over quiche QUIC. Reads H3 frames from QUIC streams (via `quic_sffi.spl`), decodes QPACK headers, dispatches to the HTTP router.

**Key types:**
```
struct H3ServerConn {
  quic:   QuicConn
  sock:   UdpSocket         // existing sync UdpSocket — runs in dedicated thread
  router: HttpRouter
}
```

**Key functions:**
```
fn h3_server_conn_new(quic: QuicConn, sock: UdpSocket, router: HttpRouter) -> H3ServerConn
fn h3_server_conn_run(sc: H3ServerConn) -> Result<(), text>
  // Poll loop:
  //   UdpSocket.recv → quic_conn_recv
  //   quic_conn_readable_streams → for each stream:
  //     quic_conn_stream_recv → h3_frame_parse (existing h3_frame.spl)
  //     HEADERS frame → qpack_decoder (existing) → HttpRouter.route → response
  //     DATA frame → body accumulation
  //   quic_conn_send → UdpSocket.send_to
fn h3_server_send_response(sc: H3ServerConn, stream_id: u64, status: u32, headers: [(text, text)], body: [u8]) -> Result<(), text>
  // qpack_encode → H3 HEADERS frame (h3_frame.spl) → quic_conn_stream_send
  // body → H3 DATA frame → quic_conn_stream_send(fin=true)
```

**Data flow:**
```
UdpSocket.recv_from(buf)
  → quic_conn_recv(conn, buf, recv_info)
  → quic_conn_readable_streams(conn) → [stream_id]
  → for each stream_id:
      quic_conn_stream_recv(conn, id, out) → (bytes, fin)
      h3_frame_parse(bytes) → H3Frame
      match frame:
        H3Frame::Headers → qpack_decode → HttpRouter.route → h3_server_send_response
        H3Frame::Data    → body buffer
  → quic_conn_send(conn, send_buf) → UdpSocket.send_to(addr, send_buf)
```

**Depends on:** `quic_sffi.spl`, `src/lib/nogc_sync_mut/http/h3/h3_frame.spl`, `src/lib/nogc_sync_mut/http/h3/qpack_encoder.spl`, `src/lib/nogc_sync_mut/http/h3/qpack_decoder.spl`, `src/lib/nogc_async_mut/io/udp.spl`.

---

## AC-3: Static File Performance

### Modify `src/lib/nogc_async_mut/http_server/static_file.spl`

Two capabilities are added on top of the existing `StaticFileHandler`: ETag/If-None-Match (304) and Range/206 partial content.

**New types added to `static_file.spl`:**
```
struct ETagValue {
  raw: text    // format: "\"<hex>\""  — strong ETag
}

struct RangeSpec {
  start: u64
  end:   u64   // inclusive; u64::MAX means "to end of file"
}

struct RangeParseResult {
  ranges: [RangeSpec]   // currently only first range used (single-range 206)
}
```

**New functions added to `static_file.spl`:**
```
// ETag generation: SHA-256 of inode + mtime_ns + file_size (no file content read)
fn static_file_etag(inode: u64, mtime_ns: u64, size: u64) -> ETagValue

// Parse "Range: bytes=start-end[,...]" header value
fn static_file_parse_range(header_value: text, file_size: u64) -> Result<RangeParseResult, u32>
  // Returns Err(416) for unsatisfiable range

// Build a 206 Partial Content response using sendfile with offset+length
fn static_file_serve_range(
  handler: StaticFileHandler,
  path: text,
  range: RangeSpec,
  file_size: u64,
  etag: ETagValue,
  caps: HttpBackendCaps
) -> Future<Result<ConnectionAction, text>>

// Check If-None-Match → return 304 if matches
fn static_file_check_etag(req_header: Option<text>, etag: ETagValue) -> bool
  // true = send 304, false = send full response
```

**Modified `StaticFileHandler.serve()` flow (extended):**
```
serve(req) →
  stat(path) → inode, mtime, size
  etag = static_file_etag(inode, mtime_ns, size)
  if req.header("If-None-Match") && static_file_check_etag(header, etag) → 304 Not Modified
  elif req.header("If-Modified-Since") && not_modified(mtime) → 304
  elif req.header("Range") →
    static_file_parse_range(header, size) →
      Ok(range)  → static_file_serve_range(...) → 206
      Err(416)   → 416 Range Not Satisfiable
  else → existing serve path (200 + sendfile/compression cache)
```

**Response headers added for ETag:**
- `ETag: "<hex>"` on all 200/206 responses.
- `Accept-Ranges: bytes` on all responses for the served file.

**Benchmark fixture path:** `test/perf/web_server_nginx_compare/`
- `harness.shs` — starts nginx + Simple server, runs `wrk`/`ab`, emits JSON result.
- `workload_gen.spl` — generates test file corpus (sizes: 1KB, 64KB, 1MB, 10MB).
- Metrics: requests/sec (RPS), p99 latency (ms), large-file throughput (MB/s).
- Nginx baseline config: `test/perf/web_server_nginx_compare/nginx_baseline.conf`.

**Depends on:** existing `static_file.spl` structs (`StaticFileHandler`, `StaticCompressionCache`, `ConnectionAction`), `http_capability_router.spl` (`HttpBackendCaps`), `src/lib/common/crypto/` (SHA-256 for ETag hash).

---

## AC-4: Unified Server — ALPN + Protocol Dispatch

### 4a. Modify `src/lib/nogc_async_mut/io/tls_handshake.spl`

**New function:**
```
fn parse_alpn_extension(ext_bytes: [u8]) -> Option<text>
  // Parses TLS ALPN extension (type 0x0010, RFC 7301).
  // ext_bytes = raw extension data field (after type + length).
  // Format: ProtocolNameList (2-byte total length + sequence of
  //   1-byte length + protocol name bytes).
  // Returns first protocol name as text, or None if empty/malformed.
  // Recognized values: "h2", "h3", "http/1.1"
```

**Modify `perform_server_handshake` return struct** (add `negotiated_protocol` field):
```
// existing TlsHandshakeResult (or equivalent return struct) gains:
  negotiated_protocol: Option<text>   // None = ALPN absent → default to "http/1.1"
```

**Inside `perform_server_handshake`:** after the extensions loop that currently slices raw bytes, add a branch:
```
if ext_type == 0x0010 {
  negotiated_protocol = parse_alpn_extension(ext_data)
}
```

**Depends on:** existing `tls_handshake.spl` extension parsing skeleton.

---

### 4b. `src/lib/nogc_async_mut/http_server/protocol_handler.spl` (new)

**Purpose:** `ProtocolHandler` trait + concrete H1/H2/H3 impls. Dispatch table keyed on ALPN string.

**Trait:**
```
trait ProtocolHandler {
  fn handle_connection(stream: AsyncTlsStream, router: HttpRouter, config: ServerConfig) -> Future<Result<(), text>>
}
```

**Concrete impls (structs with trait conformance via `impl ProtocolHandler for ...`):**
```
struct H1Handler {}
  // handle_connection: existing Connection state machine from connection.spl

struct H2Handler {}
  // handle_connection: h2_server_conn_new(stream, H2Settings.default(), router) → h2_server_conn_run()
```

**Dispatch function:**
```
fn protocol_handler_for_alpn(negotiated: Option<text>) -> Option<ProtocolHandler>
  // None or "http/1.1" → Some(H1Handler)
  // "h2"              → Some(H2Handler)
  // "h3" or unknown   → None
  //
  // NOTE: H3 is NOT dispatched here. H3 clients reach the server exclusively
  // over UDP/QUIC (via the Alt-Svc advertisement). An "h3" ALPN value on a
  // TLS-TCP stream is a client error — return None and let the caller close
  // the connection. H3 is wired in server.spl via the UDP listener path.
```

**Depends on:** `tls.spl`, `h2_server.spl`, `connection.spl`, `server.spl` types.

---

### 4c. Modify `src/lib/nogc_async_mut/http_server/worker.spl`

**Change to TLS accept path:**
```
// Before:
let stream = tls_listener.accept()
// handle as H1

// After:
let (stream, handshake_result) = tls_listener.accept_with_handshake_result()
  // tls.spl accept must return handshake result including negotiated_protocol
let handler = protocol_handler_for_alpn(handshake_result.negotiated_protocol)
handler.handle_connection(stream, router, config).await
```

**New field in `WorkerConfig`:**
```
struct WorkerConfig {
  // ... existing fields ...
  h2_settings: H2Settings   // passed to H2Handler
  enable_h2: bool
  enable_h3: bool           // controls whether UDP H3 listener is started
}
```

**Depends on:** `protocol_handler.spl`, `tls.spl` (extended `accept_with_handshake_result`), `h2_server.spl`.

---

### 4d. Modify `src/lib/nogc_async_mut/http_server/server.spl`

Add a UDP listener alongside the existing TCP listener when `enable_h3 = true`:

```
// In server main loop, alongside existing TcpListener:
if config.enable_h3 {
  let udp_sock = UdpSocket.bind(config.quic_addr)
  // Spawn h3_server_conn_run thread per incoming QUIC connection
  // (quiche demux by connection ID happens inside the worker)
}
```

**Depends on:** `h3_server.spl` (AC-2), `quic_sffi.spl`, `worker.spl` changes.

---

## Summary of new files

| File | AC | Size estimate |
|---|---|---|
| `src/lib/nogc_async_mut/http/hpack_primitives.spl` | 1 | ~120 lines |
| `src/lib/nogc_async_mut/http/h2/h2_hpack.spl` | 1 | ~250 lines |
| `src/lib/nogc_async_mut/http/h2/h2_stream.spl` | 1 | ~200 lines |
| `src/lib/nogc_async_mut/http/h2/h2_connection.spl` | 1 | ~350 lines |
| `src/lib/nogc_async_mut/http/h2/h2_server.spl` | 1 | ~200 lines |
| `src/lib/nogc_async_mut/quic/quic_sffi.spl` | 2 | ~180 lines |
| `src/lib/nogc_async_mut/quic/h3_server.spl` | 2 | ~220 lines |
| `src/lib/nogc_async_mut/http_server/protocol_handler.spl` | 4 | ~100 lines |

## Summary of modified files

| File | AC | Change |
|---|---|---|
| `src/lib/nogc_async_mut/http_server/static_file.spl` | 3 | Add ETag, Range/206 |
| `src/lib/nogc_async_mut/io/tls_handshake.spl` | 4 | Add `parse_alpn_extension`, extend result struct |
| `src/lib/nogc_async_mut/http_server/worker.spl` | 4 | ALPN dispatch, H2Settings field |
| `src/lib/nogc_async_mut/http_server/server.spl` | 4 | UDP H3 listener branch |

## Open items requiring follow-up

1. **`accept_with_handshake_result`**: `tls.spl` currently exposes `AsyncTlsListener.accept() -> AsyncTlsStream` and likely discards the handshake result. This API must be extended to return the `TlsHandshakeResult` alongside the stream. If the handshake result is structurally opaque, a thin wrapper may be needed.
2. **`rt_quiche_*` externs**: Must be added to the Rust seed runtime (`src/runtime/` or `src/compiler_rust/`) and a bootstrap rebuild run after (`scripts/bootstrap/bootstrap-from-scratch.sh --deploy`).
3. **SHA-256 for ETag**: Verify `src/lib/common/crypto/` exposes a `sha256_hex(data: [u8]) -> text` function. If absent, use `inode_mtime_size` hex-concat as a weak ETag fallback (still RFC-compliant).
4. **QPACK migration to `hpack_primitives`**: Optional in this workstream; both can coexist. File a TODO to migrate `qpack_encoder.spl`/`qpack_decoder.spl` to import `hpack_primitives.spl`.
5. **Simple syntax verification (implementer must confirm before coding):**
   - `Map<K, V>` — confirm the actual stdlib map/hash-map type name in `src/lib/common/` or `src/lib/nogc_sync_mut/`.
   - `[u8; 28]` fixed-size array syntax — confirm Simple supports it; if not, use `[u8]` with a length-invariant comment (`// always 28 bytes — sockaddr_storage`).
   - `trait` + `impl Trait for Type` — confirm the exact Simple keyword form (may be `mixin`, `conformance`, or similar per `doc/07_guide/quick_reference/syntax_quick_reference.md`).
