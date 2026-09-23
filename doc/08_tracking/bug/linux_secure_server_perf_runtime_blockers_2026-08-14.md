# Linux secure-server performance runtime blockers

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

## Source repair 2026-09-22 — verification pending

The static benchmark target in both `test/05_perf/webserver/` and its
`test/perf/webserver/` copy now calls `rt_io_tcp_listen` after a successful bind
and before printing ready or accepting requests. A listen failure closes the
socket and reports an error. The native bind prelude smoke now covers this
transition. This repairs the source-level reason a bound socket refused
connections, but a live Linux request and performance run is still required.

The PureDatabase `insert_present`/invalid-array-handle observation has no
retained native artifact or array value bits in the original receipt. Its
current compiler and storage path needs a new native reproduction before a
safe ABI fix can be identified. The bug remains OPEN.

The self-hosted CLI fails its bounded `test --help` ABI probe. A user-authorized
temporary Stage-2 build produced native HTTP and PureDatabase executables, but
the HTTP process did not install its advertised listener and the database
failed its first post-insert correctness check with an invalid-array-handle ABI
diagnostic. These failures block fair nginx/SQLite/PostgreSQL comparison and
must be fixed before performance tuning. Reproducer commands and measured
observations are retained in
`doc/09_report/perf/linux_secure_server_compare_2026-08-14.md`.

## Re-verification 2026-08-17 (app-rest lane) — UNVERIFIABLE (blocked on deploy)

This is a 13-line record whose evidence lives in
`doc/09_report/perf/linux_secure_server_compare_2026-08-14.md`. Reproducing it
requires a Stage-2 native build plus running HTTP and database servers.
`src/app/postgres_mimic_server/main.spl` is a 2.2 KB argument-parsing entry
point with no statically visible defect. Classify as blocked-on-deploy.

## Triage 2026-09-13 (BUGFIX-7 lane)

Reconfirmed blocked-on-deploy (needs a Stage-2 native build + running HTTP/DB
servers, not available to this lane). No change made.
