# DB server TCP transport buffers an unbounded request line before the byte bound is checked
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Date:** 2026-08-20
**Status:** FIXED 2026-11-03 (commit 71158ede81a)
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

## Related

- Resource-bound hardening landed 2026-08-20 (MAX_OPEN_SESSIONS,
  MAX_TXN_WRITES in server.spl/protocol.spl;
  `test/01_unit/lib/nogc_sync_mut/database/server/db_server_hardening_spec.spl`).
  Those bound state growth from WELL-FORMED frames; this bug is the byte-level
  gap below them.


## Resolution 2026-11-03

Fixed by `71158ede81a`: `TcpStream.read_line_bounded(max_bytes)`
(`src/lib/nogc_sync_mut/io/tcp.spl`) reads 1 byte per `sosix_tcp_read` and
returns Err the moment `buf.len() > max_bytes`, so buffered bytes never exceed
bound + 1 byte (tighter than bound + one chunk). `TcpDbTransport.read_message`
calls it with `MAX_REQUEST_BYTES + 1` and treats Err as connection-fatal.
Verified 2026-11-03: `bin/simple.exe test
test/01_unit/lib/nogc_sync_mut/database/server/db_server_tcp_bounded_line_spec.spl`
-> 3 total, 3 passed (real socket pair; 8193-byte and 20000-byte no-newline
payloads rejected).

Sibling sweep: `TcpStream.read_line()` is still `read_line_bounded(i64::MAX)`
(unbounded) and is called on network streams by `src/app/devhub/gui_server.spl`,
`src/app/llm_caret/main.spl`, `src/app/portal/server.spl`,
`src/app/simple_portal/server.spl`. `web_dashboard`, `llm_dashboard` login
server already use `read_line_bounded(8192)`. The four remaining callers should
move to `read_line_bounded(8192)` (follow-up; not part of this DB-server bug).
