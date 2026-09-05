# Modern web protocol profiles

This guide separates codec/profile support from live transport readiness.

| Layer | Supported | Production status |
|---|---|---|
| HTTP/2 | Typed bounded frame parsing, strict SETTINGS/WINDOW_UPDATE values, bounded increasing client-stream registry, overflow rejection, cancellation | Profile available; a live TLS/ALPN server requires its own evidence |
| HTTP/3 | Bounded frame parsing and atomic SETTINGS admission | Codec/profile only |
| QUIC | Bounded long-header admission, Version Negotiation emission, Initial key primitives, bounded contiguous CRYPTO storage | Authenticated transport blocked |
| H3 server | Compatibility type only | Terminally closed; no accept, event, or write is advertised |

## HTTP/2 parser contract

Use `h2_parse_frame_bounded(bytes, offset, max_frame_size)`. Its result is one
of `Complete(frame, consumed)`, `Incomplete(required_bytes)`,
`Ignored(consumed)`, or `Rejected(reason)`. Unknown extensions must advance by
the reported byte count. Retain bytes only for `Incomplete`; close or send the
appropriate protocol error for `Rejected`.

The default parser caps incoming frames at 16 KiB. SETTINGS entries are capped
at 64, initial windows cannot exceed 2^31-1, frame sizes must stay in the RFC
range, and WINDOW_UPDATE zero is rejected. Client stream admission accepts only
strictly increasing positive odd IDs, stops at the configured registry limit,
and refuses all new streams after cancellation/GOAWAY.

HPACK Huffman codes and lengths are immutable table owners in separate modules.
Decode uses one prefix trie, so work is linear in supplied bits rather than a
257-symbol scan for every output symbol.

## HTTP/3 frame contract

Use `h3_frame_parse_bounded` for a caller-selected payload budget; the default
is one MiB. `h3_settings_decode_strict` either returns the complete settings set
or an error. It rejects truncation, duplicates, forbidden HTTP/2 setting IDs,
and more than 64 settings. The compatibility decoder returns an empty list on
any strict error and never exposes a partial configuration.

## QUIC authority boundary

Public header parsing is structural only. Short headers are rejected without a
connection-bound DCID and header-protection owner. Protected packet emission,
Handshake/0-RTT/1-RTT payload interpretation, plaintext application emission,
and Finished-shaped state transitions are disabled. CRYPTO accumulation is
contiguous-only and capped at one MiB; cancellation is terminal and releases
stream and reassembly ownership.

Do not enable `QuicProvider.Available`, advertise H3, or label UDP carriage as
a QUIC handshake until the prerequisites in
`doc/08_tracking/bug/quic_h3_transport_tls_blocker_2026-08-20.md` pass with an
authenticated handshake and behaviorally exercised application data.
