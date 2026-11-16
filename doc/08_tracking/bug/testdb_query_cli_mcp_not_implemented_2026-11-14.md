# TestDB query: CLI, MCP and remaining TESTDB rows not implemented (2026-11-14)

Slice delivered: pure model `src/lib/common/traceability/test_query.spl` and `RunnerTestDb.query_case_attempts` (`src/lib/nogc_sync_mut/test_runner/test_db_compat.spl`).

## Remaining
- CLI `simple test query` / `test explain`: not implemented. Unblock: a facade that builds `TestQuery` and renders `TestQueryPage`.
- MCP `simple_test_query` (`src/app/mcp/**`): not implemented, out of this slice.
- TESTDB-005..010: the plan (sec 9) names them without per-row definitions available to this slice; none are covered. Spec maps TESTDB-001..004 only.
- Legacy `str_to_status` (`src/lib/nogc_sync_mut/test_runner/test_db_types.spl` ~:156) still maps unknown strings to Skipped. Not changed: callers not audited. The new query path uses `parse_test_query_status` (Unknown) instead. Unblock: audit every `str_to_status` caller, then make it fail closed.
- Query reads only `trace_case_events` rows (framework observations). Summary-table results (`test_runs`/tests status, cached results) are not yet queried, so `Cached`/`FeatureGated`/`Blocked` variants are parseable but no stored source feeds them.
- Cross-run query with no run id scans every run (O(runs x events)); acceptable for now, index later.

## Update 2026-11-15: CLI implemented
- `simple test query` / `simple test explain` landed (`src/app/test_runner_new/test_query_cli.spl`, spec `test/01_unit/app/test_runner_new/test_query_cli_spec.spl`, rows TESTDB-011..016). Verified through the seed: `bin/simple test query <path>::<case>` routes to the Simple runner (the seed passes `[test, query, ...]`, handled by `test_query_subcommand_args`); the repo DB currently holds no `trace_case_events` rows, so a real invocation reports `no rows` (exit 1). Rows were verified only against scratch DB files in the spec.
- Still open: MCP `simple_test_query` (`src/app/mcp/**`, other owner); TESTDB-005..010; summary-table sources (Cached/FeatureGated/Blocked) for the CLI; `--cursor` is a plain row offset, not an opaque/stable token across DB changes.
