# `simple test <dir>`: report generation hang and child specs run with `bin/simple`

- Status: FIXED, 2026-10-05
- Follow-up to `seed_bare_export_alias_breaks_test_dir_runner_2026-10-05.md`
  (items 1 and 2 under "Remaining")

## 1. The run hung for more than 14 minutes after printing results

**Where the time went.** It was not `update_test_database`. Probed
interpreted, the database load, update and save took about 2 s in total. The
time went into `generate_test_result_md`.
- That function calls `all_test_info()` nine times: directly, through
  `test_count_by_status`, through six `tests_by_status` calls, and through
  `flaky_test_names`.
- For every test, `all_test_info` called `db_get_suite_info`,
  `db_get_test_timing` and `db_get_test_counts`. Each of those scans a whole
  table, so the cost was O(tests × rows).
- On the repo DB (859 tests), one interpreted `all_test_info` took about
  100 s, and the whole report took 976 s.

**Fix.** `db_test_info_lookup`
(`src/lib/nogc_sync_mut/database/test_extended/database_queries.spl`)
builds one lookup table per side table: files, suites, timing and counters. It
keeps the linear helpers' semantics exactly:
- The first matching row wins.
- A suite row with an invalid `file_id` or `name_str` is skipped.

**Measured on the repo DB, interpreted.**

| what | before | after |
|---|---|---|
| one `all_test_info` | 108 s | 1.6 s |
| `generate_test_result_md` | 976 s | 22 s |
| report output | — | byte-identical to before (`cmp`) |
| full directory run of `aes/` with the DB update | more than 14 min | 105 s |

**Spec.** `test/01_unit/lib/database/test_extended_all_test_info_lookup_spec.spl`
checks on a populated DB that every field equals what the per-test helpers
return. It passes on both the old and the new code.

## 2. Child specs were spawned with `bin/simple`, not the invoking binary

**Cause.** `find_simple_binary()`
(`src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl`) identified
the running executable only through `/proc`. On macOS and BSD it fell through
to the literal path `bin/simple`, which is either the deployed binary or, in a
worktree with no `bin/simple`, a path that does not exist (every child exits
126).

**Fix.** Ask the kernel which executable our own pid is running: a bounded
`ps -o comm= -p <pid>`, canonicalised. This is the same query that
`cli_current_exe_path()` uses for the test client and the light daemon.
`SIMPLE_BINARY`, `SIMPLE_RUNTIME` and `/proc` still take precedence.

**Measured.** In a worktree with no `bin/simple`, the `aes/` directory run
went from 2 ERROR results (exit 126) to 30/30 passed.

## 3. OPEN — daemon-lane spurious timeout when several clients run at once

Seen during this change's verdict sweep: 4 parallel clients, with the daemon
lane now live since #2502. The baseline run reported
`json_coverage_spec.spl ... timeout=1 reason=daemon-worker-timeout budget_ms=730`.
- That spec passes 187/187 when run alone, on both trees.
- A budget of 730 ms means the request reached the single daemon worker with
  almost none of its budget left after waiting in the queue.
- The same queueing produced `daemon-backlog: N request(s) queued` lines on
  the other run.

This is a daemon-lane queueing defect, not something caused by this change.
Until it is fixed, verdict sweeps should run with J=1 or
`--no-session-daemon`.
