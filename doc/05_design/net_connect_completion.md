# Net Connect Completion Design

Feature: FR-NET-0001.

## Architecture

The socket table owns application-visible connect state. TCP connection state
remains in `TcpConnection`; `NetstackService` bridges the two by attaching a
connection id when SYN is queued and publishing completion only when TCP reaches
`ESTABLISHED`.

## Semantics

- TCP `connect` starts as `CONNECTING` and `in-progress`.
- Nonblocking connect returns `-EINPROGRESS`.
- Blocking connect waits on the bounded completion path.
- Poll/write readiness is derived from socket state, not from SYN queueing.
- RST/refused and timeout completions use explicit status strings.

## Verification

`test/system/net_connect_completion_spec.spl` covers success, refused, timeout,
and reset paths without requiring QEMU network availability.
