# Linux secure-server performance runtime blockers

The self-hosted CLI fails its bounded `test --help` ABI probe. A user-authorized
temporary Stage-2 build produced native HTTP and PureDatabase executables, but
the HTTP process did not install its advertised listener and the database
failed its first post-insert correctness check with an invalid-array-handle ABI
diagnostic. These failures block fair nginx/SQLite/PostgreSQL comparison and
must be fixed before performance tuning. Reproducer commands and measured
observations are retained in
`doc/09_report/perf/linux_secure_server_compare_2026-08-14.md`.
