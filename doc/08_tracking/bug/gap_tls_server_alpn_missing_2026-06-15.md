# GAP-TLS-1: Server-side ALPN is not connected to a live TLS handshake

## Triage 2026-09-13 — STILL OPEN: capability gap, nothing to close
- **measured** — `src/lib/nogc_sync_mut/http_server/tls_server.spl` still exists and is
  still the only TLS surface in that directory (no `tls_stream.spl`, no handshake or
  key-schedule module alongside it).
- **inferred** — this entry has an explicit unblock condition (a live handshake plus RFC
  known-answer evidence) and describes a thing to build, not behaviour that can stop
  reproducing. No such evidence exists in the tree. Not closable by triage.

Status: closed (2026-09-13 triage) — see the "Closed 2026-09-13" section below
Status re-verified 2026-08-17 by source inspection (triage shard 01).
Owner: Pure-Simple TLS/HTTP server lane

`src/lib/nogc_sync_mut/http_server/tls_server.spl` can choose an ALPN value
from decoded input, but no production encrypted accept path supplies the peer's
ClientHello extensions or binds the selected protocol to a live connection.

Unblock when a Pure-Simple server handshake consumes the peer ALPN extension,
selects only a configured protocol, rejects no-overlap according to policy, and
the production listener dispatches HTTP/1.1 or HTTP/2 from that negotiated
result with a live-socket SSpec oracle.

## Ground truth 2026-11-13 (lane http-20261113, tree at 6a5f8e708f2)

The ALPN feed this record called missing is now VERIFIED PRESENT:

- `src/lib/nogc_sync_mut/http_server/tls_server.spl`: `alpn_negotiate`
  (server-preference select, first-match), `alpn_from_extension_hex`
  (RFC 7301 ProtocolNameList parse), and the production dispatch surface
  `tls_server_accept` / `tls_conn_is_h2` / `tls_conn_is_http1`.
- `src/lib/nogc_async_mut/io/tls_handshake.spl`: `find_alpn_extension_data`
  (locates the ALPN ext in the ClientHello extensions block), `negotiate_alpn`
  (consumes parsed extensions during the server handshake, echoes the selection
  via `build_server_hello_bytes(..., alpn)`).
- Unit oracles: `test/01_unit/lib/nogc_async_mut/io/tls_alpn_negotiation_spec.spl`
  (h2 selected; spdy no-overlap -> ""; absent extension -> "") and
  `test/01_unit/lib/nogc_async_mut/http_server/protocol_handler_spec.spl`
  (h2 vs http/1.1 dispatch from ClientHello extensions).

STILL OPEN under this record's own unblock condition: no live-socket SSpec
oracle exists — the only system consumer
(`test/03_system/web/server/secure_pure_simple_web_server_spec.spl`) drives
`tls_server_accept` with `TcpStream.from_accepted_fd(-1)` (fake fd, fail-closed
policy checks only), and TLS 1.3 remains absent (separate GAP-TLS-2). The
2026-09-13 triage line "tls_server.spl is the only TLS surface" is outdated
(ALPN feed lives in tls_server.spl + nogc_async_mut/io/tls_handshake.spl), but
"not closable by triage" still holds. DB must stay OPEN, not closed.
