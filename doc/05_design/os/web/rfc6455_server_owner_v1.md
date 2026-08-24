# Bounded RFC 6455 server owner v1

## Scope

This is a pure-Simple prerequisite, not a `/SERVERS.ELF` integration. It owns
strict server-side upgrade validation and all WebSocket frame/fragment state.
The filesystem-launched server remains HTTP/1-only until a later connection
owner transfers the upgraded socket and any already-read tail bytes.

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

## Deferred integration

The later transport integration must validate before writing 101, preserve
HTTP read-ahead bytes through `append_tail`, keep the socket open after 101,
write returned control frames, and close exactly once on terminal state. TLS,
origin/authentication policy, routing, subprotocol and extension negotiation,
and concurrent connection admission remain outside this protocol owner.
