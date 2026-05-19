# No-Alloc TLS 1.3 Client (Baremetal)

**Version:** 0.1.0
**Status:** Implementation complete, smoke tests available
**Location:** `src/lib/nogc_async_mut_noalloc/tls/`

---

## Overview

Pure Simple TLS 1.3 client designed for baremetal targets with no heap, no OS,
and no libc dependencies. All buffers are fixed-size (stack or static).

**Cipher suite:** TLS_AES_128_GCM_SHA256 (0x1301)
**Key exchange:** X25519
**Certificate validation:** SHA-256 fingerprint pinning

## Quick Start

```simple
use std.nogc_async_mut_noalloc.tls

val root_hash = [u8; 32]  # SHA-256 of trusted root CA DER
val cfg = TlsConfig(hostname: "example.com", root_ca_hash: root_hash)

var transport = UartTransport(uart_base_addr: 0x4000_C000)
var client = TlsClient.new(cfg, transport, ephemeral_privkey)

# Handshake
client = tls_do_handshake(client, random_bytes)?

# Send application data
client = tls_send(client, payload_bytes)?

# Receive application data
val (client2, data) = tls_recv(client)?
```

## Module Structure

| File | Purpose |
|------|---------|
| `types.spl` | TLS 1.3 constants, error types, enums (TlsError, TlsState, ContentType, HandshakeType, AlertDescription) |
| `transport.spl` | Pluggable transport trait + UartTransport, MemTransport implementations |
| `aes128_gcm.spl` | AES-128-GCM encrypt/decrypt — no heap, S-box + GF(2^128) multiply |
| `x25519.spl` | X25519 ECDH key exchange with field arithmetic over GF(2^255-19) |
| `hkdf.spl` | HKDF-SHA256 extract/expand/expand_label with fixed buffers |
| `transcript.spl` | Running SHA-256 transcript hash for handshake verification |
| `key_schedule.spl` | TLS 1.3 key derivation: handshake secrets, app secrets, traffic keys |
| `record.spl` | TLS 1.3 record layer: encrypt/decrypt with sequence-number nonces |
| `handshake.spl` | ClientHello/ServerHello/Finished message construction and parsing |
| `client.spl` | Top-level TlsClient API: config, handshake, send, recv |
| `__init__.spl` | Module init with full re-exports |

## Design Constraints

- **`@no_gc`**: All storage is stack or static — no garbage collection
- **No dynamic allocation**: Fixed 16 KB record buffers, fixed-size key material
- **No OS**: Cooperative scheduling only, transport is pluggable
- **Single cipher suite**: Minimizes code size for constrained targets
- **Certificate pinning**: No X.509 parsing — validates against embedded SHA-256 hash

## Transport Trait

Implement `BaremetalTransport` to plug in your hardware:

```simple
trait BaremetalTransport
    fn send(me, data: [u8]) -> Result<Int, TlsError>
    fn recv(me, buf: [u8], max_len: Int) -> Result<[u8], TlsError>
    fn available(me) -> Int
```

Built-in implementations:
- **UartTransport** — memory-mapped UART (configure `uart_base_addr`)
- **MemTransport** — in-memory ring buffer (for testing)

## Crypto Primitives

All crypto is implemented in pure Simple with no C FFI (except SHA-256 which
uses `rt_sha256_*` runtime externs):

- **AES-128-GCM**: Full S-box, ShiftRows, MixColumns, GCM with GHASH
- **X25519**: Montgomery ladder on Curve25519, constant-time field ops
- **HKDF**: HMAC-based Extract-and-Expand per RFC 5869

## Testing

```bash
bin/simple test test/lib/nogc_async_mut_noalloc/tls/tls_smoke_spec.spl
```

9 test cases covering: error types, content types, MemTransport round-trip,
AES-128-GCM encrypt/decrypt, X25519 key exchange, HKDF, record layer,
ClientHello building, and TlsClient creation.

## Limitations

- Single cipher suite only (no negotiation fallback)
- No session resumption / 0-RTT
- No client certificates
- Certificate validation is fingerprint-only (no X.509 chain walking)
- No post-handshake messages (KeyUpdate, NewSessionTicket)
