# Network & Protocol — Agent Task Plan (2026-05-03)

## Status Summary

| Module | Standard | Status | Tests |
|--------|----------|--------|-------|
| TLS 1.3 client | RFC 8446 | Done | pass |
| TLS 1.3 server | RFC 8446 | Done | pass |
| TLS 1.3 PSK | RFC 8446 §4.2.11 | Done | pass |
| TLS 1.2 PRF | RFC 5246 §5 | Done | pass |
| HTTP/2 | RFC 9113 | Done | pass |
| HPACK | RFC 7541 | Done | pass |
| WebSocket | RFC 6455 | Done (frame layer) | pass |
| SOCKS5 | RFC 1928 | Done | pass |
| SCRAM-SHA-256 | RFC 5802 | Done | pass |
| JWT | RFC 7519 | Done | pass |
| PASETO | v4.public/local | Done | 3 ed25519 fails |
| HTTP Basic/Digest | RFC 7617/7616 | Truncated | needs retry |
| TLS KeyUpdate | RFC 8446 §4.6.3 | Not started | — |
| TLS NewSessionTicket | RFC 8446 §4.6.1 | Not started | — |
| HTTP/3 | RFC 9114 | Not started | — |
| WS permessage-deflate | RFC 7692 | Not started | — |
| STUN | RFC 8489 | Not started | — |
| SCRAM-SHA-512 | RFC 5802 ext | Not started | — |

## Implemented (12 modules)

### TLS 1.3 (`src/os/tls13/`)
- Full client handshake (ECDHE + certificates + Finished)
- Server-side handshake
- PSK (pre-shared key) connect-flow with binder computation
- 0-RTT early data framework
- Record layer encryption/decryption
- Key schedule (HKDF-based)

### HTTP (`src/os/http/` area)
- HTTP/2 connection layer + frame handling
- HPACK header compression
- HTTP Basic+Digest auth (truncated, needs retry)

### WebSocket
- Frame layer (4 commits) — text/binary/ping/pong/close

### Auth/Identity
- SCRAM-SHA-256 (RFC 5802)
- JWT (RFC 7519) — HS256, RS256, ES256
- PASETO v4 — public (Ed25519) + local (XChaCha20-Poly1305)
- HOTP/TOTP (RFC 4226/6238)
- SOCKS5 (RFC 1928)

---

## Remaining Work

### Priority 1 — TLS Extensions
| Feature | Scope | Agent Time |
|---------|-------|------------|
| TLS 1.3 KeyUpdate | Parse+emit KeyUpdate msg, re-derive traffic keys | ~45 min |
| TLS 1.3 NewSessionTicket | Server emits ticket, client stores for PSK | ~60 min |

### Priority 2 — HTTP Stack
| Feature | Scope | Agent Time |
|---------|-------|------------|
| HTTP Basic+Digest auth retry | Complete truncated W17-M work | ~30 min |
| HTTP/3 frame layer | QUIC-based H3 frame types + QPACK | ~90 min |
| WebSocket permessage-deflate | RFC 7692 compression extension | ~45 min |

### Priority 3 — Other Protocols
| Feature | Scope | Agent Time |
|---------|-------|------------|
| STUN | RFC 8489 binding request/response | ~45 min |
| SCRAM-SHA-512 | Extension of existing SCRAM-SHA-256 | ~30 min |

---

## Agent Spawn Guide

```
TLS scope:    src/os/tls13/<module>.spl
HTTP scope:   src/os/http/<module>.spl (create if needed)
Test scope:   test/unit/os/tls13/ or test/unit/os/http/
Verify:       bin/simple test test/unit/os/tls13/<spec>.spl
Dependencies: TLS needs src/os/crypto/sha256.spl, hkdf, aes128_gcm
```
