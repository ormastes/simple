# GAP-TLS-1: Server-side ALPN is not connected to a live TLS handshake

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 01).
Owner: Pure-Simple TLS/HTTP server lane

`src/lib/nogc_sync_mut/http_server/tls_server.spl` can choose an ALPN value
from decoded input, but no production encrypted accept path supplies the peer's
ClientHello extensions or binds the selected protocol to a live connection.

Unblock when a Pure-Simple server handshake consumes the peer ALPN extension,
selects only a configured protocol, rejects no-overlap according to policy, and
the production listener dispatches HTTP/1.1 or HTTP/2 from that negotiated
result with a live-socket SSpec oracle.
