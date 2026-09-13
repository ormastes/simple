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
