# TLS Simple-Server Blocker — 2026-04-17

## Summary

The "existing client ↔ Simple server" interop lane is **blocked** until
server-side TLS 1.3 is implemented in pure Simple. Current Phase 1 TLS 1.3
ships a client-only state machine.

## What works today

| Lane | Status |
|---|---|
| **Simple client ↔ rustls server** | ✅ `test/system/os_tls_system_spec.spl` (live handshake via `tools/tls_test_server/`, rustls-based) |
| **Simple client ↔ openssl s_server** | ⚪ not yet wired — see "Deferred" below |
| **Simple client ↔ BoringSSL/mbedTLS/wolfSSL/LibreSSL servers** | ⚪ installer scaffolding present (`scripts/install_ref_crypto.shs --heavy`); spec-side interop not yet written |
| **existing client ↔ Simple server** | ❌ **blocked** (no Simple server implementation) |

## Where the line is drawn

`src/os/tls13/` contains the full RFC 8446 **client** state machine:

- `tls13_connect()` / `tls13_send()` / `tls13_recv()` / `tls13_close()`
- `build_client_hello_bytes` → ClientHello
- Processes ServerHello, EncryptedExtensions, Certificate, CertificateVerify,
  server Finished
- Emits client Finished and application data records

It does **not** contain an `accept`-side entry point, ServerHello builder,
EncryptedExtensions sender, Certificate / CertificateVerify sender, or a
server-side Finished verifier. A server path needs all of those plus a
`CertificateRequest` handler for mTLS.

## What blocks progress

Per `doc/01_research/local/tls13_phase2_backlog.md` §"Server-side TLS 1.3":

> Server-side TLS is not in scope for Phase 2. Phase 1 is client-only; the
> state machine in `tls13.spl` starts with `build_client_hello_bytes` and
> processes server-initiated messages only. A server path would need an
> `accept`-side handshake entry point (ServerHello builder, EncryptedExtensions,
> Certificate/CertificateVerify sender, Finished verifier). The
> `key_schedule.spl` module is symmetric and would be reused as-is;
> `record13.spl` encrypt/decrypt are also reusable. The server state machine
> is a separate design effort; suggest treating it as a Phase 3 item.

`record13.spl` and `key_schedule.spl` **are reusable** for a server path —
their AEAD/HKDF logic is handshake-direction-agnostic.

## Deferred (non-blocked, not yet done)

- **Simple client ↔ openssl s_server interop**: extend `os_tls_system_spec.spl`
  (or add a sibling) to spawn `openssl s_server -tls1_3 -cert <cert> -key <key>`
  on a port and hit it with the Simple client. Expected to work since our
  client already handshakes against rustls. Blocked only by certificate
  fixture generation and the existing Phase-2-deferred RSA-PSS path if the
  test cert is RSA-keyed (Ed25519-keyed certs work today).
- **Intensive encode/decode at the TLS record layer**: our pure-Simple
  `chacha20_poly1305_encrypt` has a tag bug for 114-byte inputs
  (`doc/01_research/local/chacha_poly_tag_bug_2026-04-17.md`). The TLS record
  layer wraps this primitive; record-level interop tests may inherit the bug
  and must be written AFTER the primitive fix lands.

## Acceptance for unblocking

The existing-client ↔ Simple-server lane unblocks when:

1. `src/os/tls13/tls13_accept()` exists with documented semantics.
2. ServerHello / EncryptedExtensions / Certificate / CertificateVerify builders
   land in `src/os/tls13/handshake13.spl` (or a new `handshake13_server.spl`).
3. A server-side Finished verifier is added.
4. A test spec (`test/system/os_tls_server_system_spec.spl`) spawns the Simple
   server in QEMU and hits it from `openssl s_client -tls1_3`, rustls, etc.

This is a Phase 3 item per the existing backlog document.
