# HTTPS Server — Pure Simple TLS Server

**Date**: 2026-05-28
**Status**: In Progress (2026-05-29) — pure Simple approach, no Rust externs needed
**Priority**: High — gates HTTPS benchmarking, HTTP/2 ALPN, HTTP/3

## Problem (revised 2026-05-29)

Original filing assumed Rust `rustls` externs were required. However, the codebase
already has a comprehensive pure Simple crypto stack:

- AES-128/256-GCM: `src/os/crypto/aes128_gcm.spl`, `aes256_gcm.spl`
- HKDF / SHA-256 / SHA-384: `src/os/crypto/hkdf.spl`, `sha256.spl`, `sha384.spl`
- X25519 key exchange: `src/os/crypto/x25519.spl`
- Ed25519 signatures: `src/os/crypto/ed25519.spl`
- TLS 1.3 handshake (client): `src/lib/nogc_sync_mut/tls/tls_handshake.spl`
- 19 `rt_tls13_*` crypto primitives already registered

**Approach:** Implement server-side TLS 1.3 handshake as a pure Simple library
using the existing crypto primitives, then wire into the HTTP server worker.
No Rust externs needed.

## Implementation Plan (pure Simple)

1. Add `tls_server_handshake()` to `src/lib/nogc_sync_mut/tls/tls_handshake.spl`
   using existing X25519 key exchange + HKDF + AES-GCM
2. Add ALPN extraction from ClientHello for HTTP/2 negotiation
3. Wire into `src/lib/nogc_async_mut/http_server/worker.spl` for HTTPS serving
4. Add certificate loading from PEM files (DER parsing exists in `src/os/crypto/`)

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
