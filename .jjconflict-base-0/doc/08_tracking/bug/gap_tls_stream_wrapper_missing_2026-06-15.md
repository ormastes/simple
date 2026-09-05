# GAP-TLS-3: Accepted TcpStream has no encrypted Pure-Simple overlay

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 01).
Owner: Pure-Simple TLS transport lane

`src/lib/nogc_sync_mut/http_server/tls_server.spl` receives a `TcpStream`, but
there is no owned encrypted stream that frames TLS records, authenticates and
decrypts reads, encrypts writes, and preserves timeout/close behavior. The
secure server now fails closed instead of passing cleartext through.

Unblock when an owned `TlsStream`-equivalent over the existing TCP facade is
implemented and a live production-listener scenario proves encrypted request
and response bytes, invalid-record rejection, timeout handling, and clean close.
