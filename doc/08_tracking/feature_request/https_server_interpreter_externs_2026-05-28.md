# HTTPS Server — Pure Simple TLS Record-Layer

**Date**: 2026-05-28
**Updated**: 2026-05-29
**Status**: In Progress — TLS 1.2 server record-layer wired; ALPN/TLS 1.3 remain
**Priority**: High — gates HTTPS benchmarking, HTTP/2 ALPN, HTTP/3

## What Was Done (2026-05-29)

The original "Blocked" status was incorrect. The blocking assumption (Rust `rustls`
externs needed for `rt_tls_server_*`) was wrong because the worker already uses a
raw TCP `fd` path with `perform_server_handshake` — no server-accept externs needed.

**Actual state found:**
- TLS 1.2 server handshake: fully implemented in
  `src/lib/nogc_async_mut/io/tls_handshake.spl` (`perform_server_handshake`)
- `tls_decrypt_record` / `tls_encrypt_record`: implemented in worker.spl but not wired
- Worker `handle_recv` / `send_response`: had TODO stubs, session keys stored but unused
- Crypto: uses registered `rt_aes_gcm_encrypt_hex` / `rt_aes_gcm_decrypt_hex` / `rt_rsa_decrypt`
  externs (these 8 crypto externs are registered and working; not the missing 6 server-connect externs)

**Changes made to `src/lib/nogc_async_mut/http_server/worker.spl`:**
1. Added `tls_rx_buf: Dict<i64, [u8]>` accumulator field (+ init + cleanup in `close_connection`)
2. Wired TLS decrypt in `handle_recv`: accumulate raw bytes, parse 5-byte TLS record headers,
   decrypt complete records with `tls_decrypt_record`, feed plaintext to connection parser
3. Wired TLS encrypt in `send_response`: detect TLS session, chunk plaintext into
   TLS_MAX_FRAGMENT_LENGTH segments, encrypt each with `tls_encrypt_record`,
   send as single byte buffer; sendfile transparently falls back to portable-read for TLS

## Remaining Work

1. **Verification** — need `openssl s_client` or `curl https://` against interpreter mode
   to confirm handshake + encrypted GET/response round-trip. Cannot verify in this session
   (no live server run). Mark confirmed only after successful end-to-end test.

2. **ALPN** — `perform_server_handshake` is TLS 1.2 and does not negotiate ALPN.
   Worker has `TODO: [stdlib][P2] extract ALPN from handshake state when ALPN is implemented`.
   HTTP/2 over TLS requires ALPN "h2" negotiation in the handshake.

3. **TLS 1.3** — current path is TLS 1.2 + RSA key exchange. TLS 1.3 (X25519 + HKDF key
   schedule + EncryptedExtensions + CertificateVerify) is a separate handshake. The pure
   Simple crypto primitives (X25519, HKDF, AES-GCM) exist in `src/os/crypto/` but the
   server-side TLS 1.3 handshake in `tls_handshake.spl` is not yet written.

4. **TLS stack bugs** — x509 `parse_certificate_der(collection)` type mismatch,
   `fn len(collection)` shadowing (noted in original filing, still open).

## Open Decision: Crypto Provenance

The handshake and record-layer crypto uses `rt_rsa_decrypt`, `rt_aes_gcm_encrypt_hex`,
`rt_aes_gcm_decrypt_hex` (registered Rust runtime externs, separate from the missing
`rt_tls_server_create/accept/read/write` — those remain unregistered but are not needed
by the fd-based path).

**Decision needed:** should the record layer use `src/os/crypto/aes128_gcm.spl` (pure
Simple, `[u8]` API) instead of `rt_aes_gcm_*` externs?

- `aes128_gcm_encrypt(key: [u8], nonce: [u8], plaintext: [u8], aad: [u8]) -> [u8]`
- `aes128_gcm_decrypt(key: [u8], nonce: [u8], ciphertext: [u8], aad: [u8], tag: [u8]) -> Aes128GcmResult`

Wiring these requires a new hex↔[u8] bridge in `tls_common_hooks.spl` (affects client
path too). The `rt_aes_gcm_*` externs are already registered and working; switching is
purely a policy call. If "no Rust externs" means all crypto must be pure Simple, this
bridge is ~50 LOC. File as a follow-up if not required for this feature.

## Downstream Unblocks (when verification passes)

1. **HTTPS static file serving** — record-layer wired; needs live test
2. **HTTP/2 ALPN** — needs TLS 1.3 or TLS 1.2 ALPN extension support in handshake
3. **HTTP/3 / QUIC** — needs TLS 1.3 server handshake

## Related

- Report: `doc/09_report/http_server_bench_2026-05-28.md`
- Bug: self-hosted binary missing `rt_io_tcp_socket_create` (needs bootstrap redeploy)
- TLS stack bugs: x509 `parse_certificate_der(collection)` type mismatch, `fn len(collection)` shadowing
