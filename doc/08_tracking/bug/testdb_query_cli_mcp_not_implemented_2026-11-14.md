# TestDB query: CLI, MCP and remaining TESTDB rows not implemented (2026-11-14)

Slice delivered: pure model `src/lib/common/traceability/test_query.spl` and `RunnerTestDb.query_case_attempts` (`src/lib/nogc_sync_mut/test_runner/test_db_compat.spl`).

## Remaining
- CLI `simple test query` / `test explain`: not implemented. Unblock: a facade that builds `TestQuery` and renders `TestQueryPage`.
- MCP `simple_test_query` (`src/app/mcp/**`): not implemented, out of this slice.
- TESTDB-005..010: the plan (sec 9) names them without per-row definitions available to this slice; none are covered. Spec maps TESTDB-001..004 only.
- Legacy `str_to_status` (`src/lib/nogc_sync_mut/test_runner/test_db_types.spl` ~:156) still maps unknown strings to Skipped. Not changed: callers not audited. The new query path uses `parse_test_query_status` (Unknown) instead. Unblock: audit every `str_to_status` caller, then make it fail closed.
- Query reads only `trace_case_events` rows (framework observations). Summary-table results (`test_runs`/tests status, cached results) are not yet queried, so `Cached`/`FeatureGated`/`Blocked` variants are parseable but no stored source feeds them.
- Cross-run query with no run id scans every run (O(runs x events)); acceptable for now, index later.
