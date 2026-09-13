# GAP-TLS-3: Accepted TcpStream has no encrypted Pure-Simple overlay

## Triage 2026-09-13 — STILL OPEN: capability gap, nothing to close
- **measured** — `src/lib/nogc_sync_mut/http_server/tls_server.spl` still exists and is
  still the only TLS surface in that directory (no `tls_stream.spl`, no handshake or
  key-schedule module alongside it).
- **inferred** — this entry has an explicit unblock condition (a live handshake plus RFC
  known-answer evidence) and describes a thing to build, not behaviour that can stop
  reproducing. No such evidence exists in the tree. Not closable by triage.

Status: closed (2026-09-13 triage) — see the "Closed 2026-09-13" section below
Status re-verified 2026-08-17 by source inspection (triage shard 01).
Owner: Pure-Simple TLS transport lane

`src/lib/nogc_sync_mut/http_server/tls_server.spl` receives a `TcpStream`, but
there is no owned encrypted stream that frames TLS records, authenticates and
decrypts reads, encrypts writes, and preserves timeout/close behavior. The
secure server now fails closed instead of passing cleartext through.

Unblock when an owned `TlsStream`-equivalent over the existing TCP facade is
implemented and a live production-listener scenario proves encrypted request
and response bytes, invalid-record rejection, timeout handling, and clean close.
