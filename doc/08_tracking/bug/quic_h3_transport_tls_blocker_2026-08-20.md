# QUIC/HTTP-3 transport blocker (2026-08-20)

Status: blocked; H3 advertisement remains hard-disabled by
`nogc_async_mut.quic.quic_provider.quic_provider_check()` returning
`QuicProvider.Unavailable`.

The earlier strict-visibility blocker is closed: `crypto_sffi` now exports its
existing nullable `random_hex` production facade, and `quic_transport.spl`
keeps exact lower-case/length/nonzero/uniqueness admission. Entropy failure
still returns no connection key. This does not change the overall blocked
status because authenticated QUIC/TLS and H3 lifecycle prerequisites below are
still absent.

## Bounded protocol-profile hardening landed 2026-08-20

- QUIC long-header admission now rejects oversized/truncated connection IDs,
  bad fixed bits, truncated tokens/payloads, malformed version-negotiation
  lists, and packet-length underflow. Short headers fail closed without the
  connection-bound DCID and header-protection context.
- Plaintext Handshake/1-RTT bytes no longer advance the connection or TLS
  state. A Finished-shaped byte sequence is not application-key authority, and
  plaintext application emission returns no packet.
- CRYPTO accumulation is contiguous-only, capped at one MiB, and append-linear;
  peer-selected gaps can no longer allocate zero-filled memory.
- HTTP/3 frame parsing has a caller-selected payload bound. Strict SETTINGS
  decode rejects truncation, duplicates, the forbidden HTTP/2 identifier range,
  and more than 64 entries without returning a partial configuration.

These are fail-closed wire/profile guarantees, not an H3-ready transport claim.

## Exact blockers

- `src/lib/nogc_async_mut/io/quic/quic_connection.spl`: the TLS 1.3
  handshake state machine does not consume/produce TLS handshake records or
  authenticate the peer, and does not install handshake/application traffic
  keys. `QuicTlsState.Connected` can therefore not be reached from a verified
  wire handshake. The previous plaintext state transitions are now disabled.
- `src/lib/nogc_async_mut/quic/h3_server.spl`: the compatibility facade now
  returns terminal `Closed`; accept/process/respond perform no provider calls
  or writes. A future implementation must replace this fail-closed surface
  with a real connection rather than treating its zero handle as accepted.
- `src/lib/nogc_async_mut/io/quic/quic_transport.spl`: client connection IDs
  now use the checked `crypto_sffi.random_hex` OS-CSPRNG facade with
  exact-length/hex validation and
  return an empty key on entropy failure. Existing server demux uses the
  peer-provided destination ID; it still requires authenticated QUIC state
  before service dispatch.
- `src/lib/nogc_async_mut/io/quic/quic_crypto.spl`: AES header protection is
  available and covered by the RFC 9001 vector test, but this does not replace
  the missing TLS handshake/application-key integration.

## Required prerequisites before unblocking

1. Add a real TLS 1.3 provider (certificate/hostname verification, transcript,
   Finished verification, and QUIC CRYPTO record integration) with bounded
   handshake buffering and fail-closed errors.
2. Install handshake and 1-RTT packet keys only after verified TLS state;
   reject protected packets at unavailable encryption levels.
3. Replace the H3 placeholder lifecycle with a real UDP receive/accept path;
   never call transport operations with a zero handle.
4. Add wire tests for malformed/oversized CRYPTO frames, authentication
   failure, downgrade attempts, timeout, and application-key transition.

## Resume command

After the prerequisites exist, run:

```sh
bin/simple test test/01_unit/lib/nogc_async_mut/io/quic --mode=interpreter
bin/simple test test/01_unit/lib/nogc_async_mut/quic --mode=interpreter
```

Then update `quic_provider_check()` only when those tests plus an end-to-end
authenticated QUIC-TLS handshake pass; do not advertise H3 based on framing,
header protection, or QPACK tests alone.

## Current verification authority

The scoped source/diff/stub/file-size checks pass. Executable Simple specs,
docgen, and optimizer evidence remain unrun: the workspace `bin/simple` is a
Rust-built seed and no admitted Stage 3/4 self-hosted test runtime exists.
Stage 2 compiler evidence is not SSpec authority.

## Provider gate wired 2026-08-21 (still blocked overall)

`quic_provider.spl` documented that "native quiche calls go through
quic_connection.spl only when the provider reports Available", and prerequisite
3 above says transport operations must never be called with a zero handle.
Neither was true: `quic_provider_check` / `quic_provider_gate` had **zero call
sites**, every `pub fn` in `src/lib/nogc_async_mut/quic/quic_connection.spl`
dispatched to `rt_quic_*` unconditionally, and `quic_accept`/`quic_connect`
returned the raw handle without ever inspecting it — so a failed (0/negative)
handle was handed straight back to the runtime on the next call.

Fix (`quic_connection.spl`, `__init__.spl`): new `quic_connection_is_usable`
gates on `quic_provider_is_usable(quic_provider_check())`, `not closed`, and
`handle > 0`. Constructors return a terminal `_quic_closed_connection` without
touching an extern when the provider is unusable or the handle is non-positive;
every operation refuses an unusable connection (no datagram in, no bytes out,
`-1` from `quic_stream_send`/`quic_timeout_millis`) instead of calling
`rt_quic_*`.

Evidence — `test/01_unit/lib/nogc_async_mut/quic/quic_connection_provider_gate_spec.spl`
(exercises the real module, no inlined copy):

- pre-fix (module reverted): `Results: 13 total, 1 passed, 12 failed`
- post-fix: `SPEC FILE VERDICT: ... outcome=OK declared>=13 executed=13 passed=13 failed=0`

This closes prerequisite 3's zero-handle clause only. Prerequisites 1, 2 and 4
(a real TLS 1.3 provider, verified-state key installation, and the
authentication/downgrade wire tests) are untouched, so the record stays
**blocked** and `quic_provider_check()` still returns `Unavailable`.
