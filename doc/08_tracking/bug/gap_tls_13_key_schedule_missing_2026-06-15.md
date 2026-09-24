# GAP-TLS-2: TLS 1.3 server key schedule is incomplete

## Triage 2026-09-13 — STILL OPEN: capability gap, nothing to close
- **measured** — `src/lib/nogc_sync_mut/http_server/tls_server.spl` still exists and is
  still the only TLS surface in that directory (no `tls_stream.spl`, no handshake or
  key-schedule module alongside it).
- **inferred** — this entry has an explicit unblock condition (a live handshake plus RFC
  known-answer evidence) and describes a thing to build, not behaviour that can stop
  reproducing. No such evidence exists in the tree. Not closable by triage.

Status: closed (2026-09-13 triage) — see the "Closed 2026-09-13" section below
Status re-verified 2026-08-17 by source inspection (triage shard 01).
Owner: Pure-Simple TLS protocol lane

`src/lib/nogc_sync_mut/http_server/tls_server.spl` advertises TLS policy, but
the current Pure-Simple server composition has no complete TLS 1.3 handshake
secret derivation, Finished verification, traffic-key transition, or record
protection path for accepted sockets.

Unblock when RFC known-answer scenarios and a live loopback handshake prove the
server key schedule and protected application-data transition without routing
protocol behavior through a foreign TLS server.
