# Bounded RFC 6455 server owner v1

## Scope

This pure-Simple owner is integrated into `/SERVERS.ELF` for plaintext `ws://`
connections. It owns strict server-side upgrade validation and all WebSocket
frame/fragment state. The HTTP framer transfers any bytes read after the header
terminator as one bounded 8,192-byte tail; ordinary HTTP body framing is unchanged.

## Contract

`validate_rfc6455_server_handshake` accepts only strict-CRLF `GET HTTP/1.1`
requests with exactly one non-empty `Host`, one version and one key field, plus
HTTP list-valued `Upgrade` and `Connection` fields containing the required
tokens. Version is 13. The key must be canonical padded RFC 4648 for
exactly 16 decoded bytes. Success returns the complete 101 response.
The handshake is bounded to 65,550 bytes, 8,192 bytes per request/header line,
and 100 fields before any response is authorized. Host syntax and binding to a
configured authority remain prerequisites of the enclosing HTTP owner; this
protocol owner requires exactly one non-empty Host but does not overclaim that
as authority validation.

`Rfc6455ServerConnectionOwner.append_tail` is the sole input boundary. It
supports arbitrarily fragmented frames across calls and explicitly accepts bytes retained by
a future HTTP-to-WebSocket handoff. Client frames must be masked. RSV bits,
reserved opcodes, non-final or oversized control frames, non-canonical extended
lengths, and a set 64-bit length MSB fail closed with code 1002. Invalid UTF-8
fails with 1007 and size violations with 1009.

Messages are bounded to 65,536 payload bytes. The wire buffer is bounded to
65,550 bytes: maximum payload plus the 14-byte masked 64-bit frame header.
One message is bounded to 1,024 fragments. Control payloads are at most 125
bytes. Ping produces an unmasked Pong with the
identical payload. Peer Close is validated, echoed once, and makes the owner
terminal. Protocol failure emits one unmasked Close and makes it terminal.
Each call accepts at most the existing 8,192-byte socket-read quantum and can
return at most 1,367 events. Larger transport reads must be chunked before this
boundary, preventing valid many-tiny-frame input from growing an unbounded
result array.

## Ownership and complexity

The owner is single-connection mutable state and must never cross execution
domains. A read cursor processes every frame in place and compacts at most once
per bounded drain, avoiding per-frame remainder copies; processing is O(n).
Retained wire and message storage are separately bounded.
No runtime calls, global state, sockets, filesystem access, or hidden retries
exist in the owner.

## Transport integration

The handler admits only exact `/ws` upgrades, validates before writing 101,
transfers HTTP read-ahead through `append_tail`, and moves the socket into one
bounded `WebSocketTransportOwner`. That owner performs at most one receive per
outer HTTP/DB service iteration, writes every returned Pong/Close, emits 1001
before idle-policy or server shutdown, and closes its fd at most once. A hard
transport error closes immediately without a retry spin. Only one WebSocket is
admitted at a time; further upgrades fail before 101. Text and binary messages
are consumed but no application message service is claimed. TLS,
origin/authentication policy, subprotocol and extension negotiation remain
outside this protocol owner. Until an origin allowlist exists, every request
carrying `Origin` is rejected to prevent browser ambient-authority upgrades.
The non-browser development endpoint remains unauthenticated; therefore WSS or
production service is not claimed.
