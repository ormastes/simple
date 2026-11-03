# WebSocket handshake nonce entropy

Status: **AUTHORED_UNRUN**. This manual was authored from the SSpec, not generated
by a successful execution. Runtime RED/GREEN and branch coverage are unavailable;
TDD is incomplete. No admitted Simple producer/runtime was used.

Source: `test/01_unit/lib/nogc_sync_mut/websocket/websocket_nonce_entropy_spec.spl`

Source SHA-256: `769128f3aebb05e24397a6a8fe9b54f4644a4f586de0e97d6e9922780fda58f0`

Contract: [RFC 6455 section 4.1](https://www.rfc-editor.org/rfc/rfc6455.html#section-4.1)
requires a randomly selected 16-byte nonce encoded with Base64. Production calls
the existing `entropy_platform_bytes(16u64)` owner. Its failure must reach the
CDP caller before an upgrade request is written; no empty or time-derived fallback.

| Authored scenario | Oracle | Execution |
|---|---|---|
| Preserve sixteen binary octets | Repeated 00/7f/80/ff encodes to `AH+A/wB/gP8Af4D/AH+A/w==` | UNRUN |
| Provider error | Exact error preserved; no nonce returned | UNRUN |
| Exact length | Reject 0/15/17; accept sixteen zero octets | UNRUN |
| Production entropy owner | Successful nonce has 24 Base64 characters and `==` suffix | UNRUN |

The binary vector oracle was independently checked with .NET Convert; that
check does not execute the Simple implementation. The shape test does not prove
randomness. Four examples are authored, zero examples are recorded as executed.

Pending validation: run these examples on an admitted Simple runtime, bind
producer/source/provider hashes, inject actual entropy failure through CDP and
assert zero request bytes plus socket closure, and measure coverage. There is no
runtime failure reproduction or no-send receipt in this candidate.

The canonical bug `websocket_timestamp_owner_and_entropy_2026_10_16` remains OPEN:
frame masking still uses its historical predictable formula. This candidate
changes only handshake nonce generation and its sole production caller.
