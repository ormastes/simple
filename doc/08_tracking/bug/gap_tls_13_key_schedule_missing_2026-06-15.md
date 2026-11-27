# GAP-TLS-2: TLS 1.3 server key schedule is incomplete

## Triage 2026-09-13 — STILL OPEN: capability gap, nothing to close
- **measured** — `src/lib/nogc_sync_mut/http_server/tls_server.spl` still exists and is
  still the only TLS surface in that directory (no `tls_stream.spl`, no handshake or
  key-schedule module alongside it).
- **inferred** — this entry has an explicit unblock condition (a live handshake plus RFC
  known-answer evidence) and describes a thing to build, not behaviour that can stop
  reproducing. No such evidence exists in the tree. Not closable by triage.

Status: OPEN (capability gap; the "closed (2026-09-13 triage)" line below was
wrong — that triage found the gap STILL OPEN. Corrected 2026-11-25.)
Status re-verified 2026-08-17 by source inspection (triage shard 01).
Owner: Pure-Simple TLS protocol lane

`src/lib/nogc_sync_mut/http_server/tls_server.spl` advertises TLS policy, but
the current Pure-Simple server composition has no complete TLS 1.3 handshake
secret derivation, Finished verification, traffic-key transition, or record
protection path for accepted sockets.

Unblock when RFC known-answer scenarios and a live loopback handshake prove the
server key schedule and protected application-data transition without routing
protocol behavior through a foreign TLS server.

## Triage 2026-11-25 (worktree work/p2w2-ah-20261125, source inspection) — STILL OPEN

- The header previously read "Status: closed (2026-09-13 triage)", but the
  2026-09-13 triage section itself concludes "STILL OPEN: capability gap,
  nothing to close". The header was wrong and has been corrected to OPEN.
- Re-inspected today: `src/lib/nogc_sync_mut/http_server/tls_server.spl`
  still carries the GAP-TLS-2 comment block ("No TLS 1.3 key schedule — the
  tls/ library implements TLS 1.2 … TLS 1.3 (HKDF-based key schedule, ECDHE,
  AEAD record) is absent", tls_server.spl:34-36) and still declares no
  key-schedule, HKDF, traffic-secret or Finished-derivation code (245 lines,
  config/ALPN/conn composition only).
- Classification unchanged: this is a build-out (TLS 1.3 handshake secret
  derivation, Finished verification, traffic-key transition, record
  protection) gated on RFC known-answer + live loopback evidence — a program,
  not a bounded P2 fix. Left OPEN, no code change attempted.
