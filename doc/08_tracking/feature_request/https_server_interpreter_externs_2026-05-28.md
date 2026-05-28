# HTTPS Server — Missing Interpreter Externs

**Date**: 2026-05-28
**Status**: Blocked
**Priority**: High — gates HTTPS benchmarking, HTTP/2 ALPN, HTTP/3

## Problem

Server-side TLS externs are declared in `src/lib/nogc_sync_mut/io/tls_sffi.spl` (35 total)
but only 5 are registered in the Rust seed interpreter — all client-side.
No server-side TLS externs are implemented, blocking HTTPS serving in interpreter mode.

## Missing Externs (6 core, in priority order)

| Extern | Purpose | Signature |
|--------|---------|-----------|
| `rt_tls_server_create` | Create rustls server config + listener | `(port: i64, cert_path: text, key_path: text) -> i64` |
| `rt_tls_server_accept` | Accept + TLS handshake, return conn handle | `(server: i64) -> i64` |
| `rt_tls_server_read` | Decrypt + read from TLS connection | `(conn: i64, max_bytes: i64) -> text` |
| `rt_tls_server_write` | Encrypt + write to TLS connection | `(conn: i64, data: text) -> i64` |
| `rt_tls_server_shutdown` | Close TLS listener | `(server: i64) -> i64` |
| `rt_tls_server_config_set_alpn` | Set ALPN protocols (h2, http/1.1) | `(config: i64, protocols: text) -> i64` |

## Implementation Location

- Register in: `src/compiler_rust/compiler/src/interpreter_extern/mod.rs`
- Implement in: `src/compiler_rust/compiler/src/interpreter_extern/native_net/` (new file or extend existing)
- Dependency: `rustls` crate (check if already in Cargo.toml)
- Reference: existing client externs in `interpreter_native_net::rt_tls_client_*`

## Currently Registered (5/35)

- `rt_tls_client_connect` / `rt_tls_client_connect_with_sni`
- `rt_tls_client_write` / `rt_tls_client_read` / `rt_tls_client_close`
- 19 `rt_tls13_*` crypto primitives (SHA-256, HKDF, AES-GCM, Ed25519)

## Downstream Unblocks

1. **HTTPS static file benchmarks** — direct Simple HTTPS serving (estimated ~44K RPS native, ~400 RPS interpreter)
2. **HTTP/2 ALPN negotiation** — `dispatch_by_alpn()` in worker.spl needs ALPN from TLS handshake
3. **HTTP/2 server integration** — H2Connection + HPACK exists (~10 files), worker has partial h2 handlers, needs ~150 LOC to wire:
   - `src/lib/nogc_async_mut/http_server/worker.spl`: route OP_RECV on h2_connections to handle_h2_recv()
   - `src/lib/nogc_sync_mut/tls/tls_handshake.spl`: extract ALPN from handshake result
   - `src/lib/nogc_async_mut/http/h2/h2_connection.spl`: minor integration fixes
4. **HTTP/3 / QUIC** — needs TLS 1.3 server handshake for QUIC transport

## Related

- Report: `doc/09_report/http_server_bench_2026-05-28.md`
- Bug: self-hosted binary missing `rt_io_tcp_socket_create` (needs bootstrap redeploy)
- TLS stack bugs: x509 `parse_certificate_der(collection)` type mismatch, `fn len(collection)` shadowing
