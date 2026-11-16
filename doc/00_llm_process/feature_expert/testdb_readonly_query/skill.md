# Feature expert: TestDB read-only query

## What exists
- Pure model: `src/lib/common/traceability/test_query.spl` — typed case key, run id, planned-case identity (`Recorded`/`Missing`), attempt identity (`StreamOrder`/`Missing`), `TestQueryStatus` (incl. `Unknown(raw)`), `TestQualification` (only `Passed` is `Pass`), bounded pagination (`TestQueryLimit` 1..1000, `TestQueryCursor{token}`: opaque `tq1:<sha256 of case+run+limit+row snapshot>:<offset>`; plain integers, tampered tokens, other queries and changed snapshots are `InvalidQuery`, CLI exit 2), typed `TestQueryTruncation`/`TestQueryCoverage`, `TestQueryError{kind,detail}`.
- DB method: `RunnerTestDb.query_case_attempts(query)` in `src/lib/nogc_sync_mut/test_runner/test_db_compat.spl`. Read-only (uses `list_runs`, `get_trace_case_events`, `get_trace_run_plan`; never saves). Corrupt trace table -> `StoreUnreadable`; unknown run id -> `UnknownRun`.
- Layering: pure types live in `common`; only the DB method touches `nogc_sync_mut`.

## Rules
- Each started/finished pair is its own attempt row; unclosed start = `NotFinished` (coverage Partial); finished without start = attempt `Missing`.
- New path never maps unknown status text to Skipped; legacy `str_to_status` (test_db_types.spl) is untouched.
- Rows are unverified framework observations, never admitted evidence.

## Specs
- `test/01_unit/lib/common/traceability/test_query_spec.spl` (pure, 11)
- `test/01_unit/lib/test_runner/test_db_query_spec.spl` (in-memory RunnerTestDb, 4)

## Not done
See `doc/08_tracking/bug/testdb_query_cli_mcp_not_implemented_2026-11-14.md`.

## CLI: `simple test query` / `simple test explain`
- Module: `src/app/test_runner_new/test_query_cli.spl` (pure `parse_test_query_args`, `render_test_query_page`, `render_test_explain_page`, `render_test_query_outcome`; I/O only in `open_test_db_read_only` / `execute_test_query`). Hooked at the top of `run_test_cli` in `test_runner_main.spl` via `test_query_subcommand_args` (accepts the dispatcher's leading `test` token); plain `test <path>` is untouched.
- Usage: `simple test query <path>::<case> [--run <id>] [--limit N] [--cursor C] [--format table|sdn]`, `simple test explain <path>::<case> [--run <id>]`. Defaults: table, limit 50 (explain 1000, no cursor).
- Exit codes (plan silent, chosen here): 0 rows found, 1 no rows, 2 usage error / unknown run / missing, corrupt or unsealed DB. Typed `TestQueryExitDecision` -> `TestQueryExitCode`.
- Read-only: `open_test_db_read_only` requires the file to exist (no cold-start create, no `load_with_migration`), calls `load_test_database_extended`, never `save`. Spec compares bytes, mtime, `.wal` presence and directory listing before/after.
- Truncation prints `partial: truncated` + `next cursor: <token>`; Partial coverage prints `partial: some attempts ...`. `explain` gives a reason per status (skipped/cached/blocked/unknown never qualify) and `identity missing: ...`.
- Spec: `test/01_unit/app/test_runner_new/test_query_cli_spec.spl` (TESTDB-011..016).
- Routing: the Rust seed's `test` dispatch falls through to `src/app/test_runner_new/main.spl`, so `bin/simple test query ...` reaches this code; direct form `bin/simple run src/app/test_runner_new/main.spl query ...` also works.
