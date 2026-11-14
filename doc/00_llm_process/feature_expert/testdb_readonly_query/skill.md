# Feature expert: TestDB read-only query

## What exists
- Pure model: `src/lib/common/traceability/test_query.spl` — typed case key, run id, planned-case identity (`Recorded`/`Missing`), attempt identity (`StreamOrder`/`Missing`), `TestQueryStatus` (incl. `Unknown(raw)`), `TestQualification` (only `Passed` is `Pass`), bounded pagination (`TestQueryLimit` 1..1000, `TestQueryCursor`), typed `TestQueryTruncation`/`TestQueryCoverage`, `TestQueryError{kind,detail}`.
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
