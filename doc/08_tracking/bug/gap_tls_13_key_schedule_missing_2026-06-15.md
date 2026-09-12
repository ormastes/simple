# GAP-TLS-2: TLS 1.3 server key schedule is incomplete

Status: CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)
Status re-verified 2026-08-17 by source inspection (triage shard 01).
Owner: Pure-Simple TLS protocol lane

`src/lib/nogc_sync_mut/http_server/tls_server.spl` advertises TLS policy, but
the current Pure-Simple server composition has no complete TLS 1.3 handshake
secret derivation, Finished verification, traffic-key transition, or record
protection path for accepted sockets.

Unblock when RFC known-answer scenarios and a live loopback handshake prove the
server key schedule and protected application-data transition without routing
protocol behavior through a foreign TLS server.

## Triage 2026-09-12
Rule C: record predates 2026-07-29 (>=45 days) and carries no repro that ran conclusively within the triage budget; closed stale per the standing 'too old -> close' decision. Binary (unused, no run needed): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
