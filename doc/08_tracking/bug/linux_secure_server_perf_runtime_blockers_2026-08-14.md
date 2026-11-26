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

## Verification 2026-11-26 (Linux x86_64, lane 4)

- **HTTP static server (`test/05_perf/webserver/static_file_server.spl`):**
  - `static_listener_publication_contract_spec.spl --mode=interpreter` PASS (2/2, outcome=OK).
  - Stage-2 native build (`--entry-closure --entry test/05_perf/webserver/static_file_server.spl`) succeeded; live server bound `127.0.0.1:18999`, served 3/3 HTTP/1.1 `200 OK` responses (52,245 bytes each for `README.md`), and exited `RC=0` (`[simple-static-server-ready]` / `[simple-static-server-done] served=3`).
- **PureDatabase CRUD driver (`test/05_perf/bench/db_crud_compare_driver.spl`):**
  - Bootstrap seed interpreter exited `2` at `stage=insert` with `validation_failed=insert_present` (matching `dbrow_option_native_probe.spl` / `db_crud_native_probe.spl` where `row.?` renders `<invalid-heap:...>` in the seed interpreter).
  - Stage-2 native build of `db_crud_compare_driver.spl` was deferred/cancelled during concurrent P3a bootstrap when host `MemAvailable` dipped to ~8 GiB. Host lacks `nginx`, `wrk`, `sqlite3`, and `psql`. Status stays OPEN (P2).

## Verification 2026-11-26 (Linux aarch64, DGX GB10): still OPEN

Tip `79445b063c4`, Rust seed sha256 prefix `fb80903917d6d5f5`.

- **The DB `insert_present` failure was a driver bug, not a PureDatabase
  bug.** `db_crud_compare_driver.spl:37` compared `row.?` with `want: bool`.
  `.?` returns `T?` (a pass-through, per
  `syntax_quick_reference.md` § Existence Check), so the comparison was never
  equal. The `<invalid-heap:…>` text is just how the seed prints a class
  value: `row.unwrap()` and a plain class instance print the same way.
  - Fix: `row.is_some() != want` at `:37`, and `row.is_none()` at `:72`.
  - Seed run: rc 2 -> 0, and all five stages pass (insert 556 us, where 103,
    update 189, delete 252, txn 265).
- **HTTP:** `static_listener_publication_contract_spec.spl` passes 2/2 on
  aarch64.
- **Native: not verified.** The Stage 2 built from `cd29cfa8b64c`
  (`stage2-admitted`, 2026-11-22) cannot native-build the driver closure, on
  tip or on its own pinned tree. MIR/codegen ICEs block the link, in
  `common.encoding.external_text`, `common.search.ranking`,
  `db.dbfs_engine.fts.search`, `io.external_file` and
  `io.file_text_session`. So two things are still unproven on aarch64: the
  original native invalid-array-handle, and the live HTTP listener. Whether
  the native diagnostic was this same driver comparison is open.
- **Checker gap (not filed):** the seed accepts `i64? != bool` without a
  type error. That is how this driver bug went unnoticed.
