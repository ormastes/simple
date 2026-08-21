# DB server TCP transport buffers an unbounded request line before the byte bound is checked

**Date:** 2026-08-20
**Status:** RESOLVED 2026-08-21
**Severity:** Medium (remote memory-exhaustion vector on the production transport)
**Component:** `std.database.server` transport

## Defect

`MAX_REQUEST_BYTES` (8192, `src/lib/nogc_sync_mut/database/server/protocol.spl:46`)
is enforced only inside `parse_request` — i.e. AFTER the whole request line has
already been read into memory. The production transport's read path,
`TcpDbTransport.read_message` (`src/lib/nogc_sync_mut/database/server/transport.spl:58-64`),
calls `stream.read_line_nullable()` with no byte bound, so a client that sends
gigabytes without a newline makes the server buffer all of it before the
protocol layer ever gets a chance to answer `ERR_MALFORMED`.

The fail-closed contract in protocol.spl ("every malformed input returns an
ERR response") holds at the frame level but is fail-open at the byte level: the
oversized frame is rejected, but only after being fully materialised.

## Why not fixed minimally now

`read_line_nullable()` (std.nogc_sync_mut.io.tcp.TcpStream) exposes no
max-length variant. A correct fix needs a bounded line read at the stream API
level (e.g. `read_line_bounded(max_bytes)` returning an error/EOF once the
bound is crossed, plus draining or dropping the connection), which is a stream
API change, not a server-tier guard. Truncating in the transport without stream
support would silently split one oversized frame into several bogus frames.

## Unblock condition

Add a bounded line-read to `TcpStream` (or a wrapper), use it from
`TcpDbTransport.read_message` with `MAX_REQUEST_BYTES + 1`, and treat a
bound-crossing read as a connection-fatal error (close, never re-frame).
Regression spec should drive a >8192-byte no-newline payload against
`serve_tcp` and assert the connection closes without unbounded buffering.

## Resolution 2026-08-21

Added `TcpStream.read_line_bounded(max_bytes)` in
`src/lib/nogc_sync_mut/io/tcp.spl:278` — reads one byte at a time via the
existing `rt_io_tcp_read`, appends via `io_append_chunk`, and fails closed
(`Err`) the instant the accumulated line exceeds `max_bytes`, before a
newline is ever required. `TcpDbTransport.read_message`
(`src/lib/nogc_sync_mut/database/server/transport.spl`) now calls
`stream.read_line_bounded(MAX_REQUEST_BYTES + 1)` instead of the unbounded
`read_line_nullable()`; any bound-crossing (or other) read error closes the
connection and returns `nil` rather than re-framing partial data as a bogus
request — connection-fatal, never a partial reparse, per the unblock
condition above.

Reproduce spec (real sockets, not mocks):
`test/01_unit/lib/nogc_sync_mut/database/server/db_server_tcp_bounded_line_spec.spl`
— `Results: 3 total, 3 passed, 0 failed`. Covers: a normal line at/under the
bound still succeeds; `TcpStream.read_line_bounded` fails closed on an
over-cap no-newline payload; `TcpDbTransport.read_message` closes the
connection (returns `nil`) rather than buffering an unbounded no-newline
line sent over a real `TcpDbListener`/`TcpStream` pair.

Regression: `test/01_unit/lib/nogc_async_mut/net/net_tcp_facade_spec.spl` ->
`Results: 4 total, 4 passed, 0 failed`.

## Related

- Resource-bound hardening landed 2026-08-20 (MAX_OPEN_SESSIONS,
  MAX_TXN_WRITES in server.spl/protocol.spl;
  `test/01_unit/lib/nogc_sync_mut/database/server/db_server_hardening_spec.spl`).
  Those bound state growth from WELL-FORMED frames; this bug is the byte-level
  gap below them.
