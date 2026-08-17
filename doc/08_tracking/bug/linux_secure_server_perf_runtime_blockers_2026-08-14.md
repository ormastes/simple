# Linux secure-server performance runtime blockers

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

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
