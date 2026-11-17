# Traceability / bug / MCP / skills plan 2026-11-14 — remaining gaps after waves 1–3

Date: 2026-11-16. Release line: `release/1.0.0`.
Plan: `simple_traceability_spipe_bug_mcp_skills_improvement_plan_2026-11-14.md`.

This record collects the open items that have no other bug record. Items that
already have their own record are listed at the end by path only.

## 2. Public primitives in the traceability model — closed

Re-checked 2026-11-17 on `release/1.0.0`: `TraceLocator`, `TraceClaim`,
`TraceEdge`, `SnapshotSubject`, `TraceDiagnostic` and `TraceNode` hold only
bare `text` fields or enums, and `TraceReverseIndexV1.by_key` is
`Dict<text, [TraceEntityIdV1]>`. No `i64`/`bool`/`u8` public field is left.
Bare `text` is exempt from the primitive rule (owner decision), so these
structs meet the requirement as they stand.

Closed-set `text` field that could become an enum if the exemption is ever
narrowed: `TraceDiagnostic.severity` (error, warning). `TraceLocator.locator_kind`
is now the closed enum `TraceLocatorKind` (text only at the SDN boundary via
`locator_kind_name` / `parse_locator_kind`); the graph wire DTO
`TraceGraphLocatorV1.locator_kind` stays `text` and is validated by
`graph_schema_v1.spl`.

## 3. MCP / ctx

- `simple_ctx_purge` is a compare-and-swap on the store generation key, but an
  append that lands between the final key check and the rename still targets
  the replaced file and is lost (`src/app/mcp/main_lazy_ctx_tools.spl`,
  `ctx_purge_commit`). Unblock: an OS compare-and-rename, or appends that
  re-check the generation after writing.

## 4. Test query and harness

- The plan (sections 3.5, 9.1) lists `TESTDB-001`..`TESTDB-010` as one range with
  no per-id rows. The per-id definitions, taken only from what the plan states,
  now live in the header of `test/01_unit/lib/common/traceability/test_query_spec.spl`:
  001 exact query, 002 status variants, 003 provenance/missing identity, 004
  pagination and rejected queries, 005 read-only/no-write isolation, 006 failed
  authoritative query is a typed error not an empty success, 007 retries stay
  separate, 008 skipped/cached/expired never PASS, 009 CLI/MCP parity
  with `RunnerTestDb`, 010 requirement/bug-scoped queries. 001-009 each have a
  tagged scenario.
- `TESTDB-010` is only defended fail-closed: `simple test query` has no
  `--bug`, `--requirement` or `--levels` (unknown-flag usage error,
  `src/app/test_runner_new/test_query_cli.spl:143`), and `simple_test_query` takes
  only `path`/`name` (`src/app/mcp/main_lazy_trace_tools.spl:301`). Plan 3.2 and
  acceptance item 2 (`--bug=<id>` returns case definitions, run attempts,
  executable/source identity, missing evidence) are not implemented. Unblock: a
  bug/requirement -> case resolver over the traceability graph feeding
  `RunnerTestDb.query_case_attempts`.
- Plan 3.5 return fields beyond the current row (`test_definition_digest`,
  `binary_digest`, `host/backend`, `started_at`, `duration`, `failure_code`,
  `artifact_refs`, `level`) are not in `TestQueryRow`; rows carry run, planned
  case, attempt, status, qualification and provenance only
  (`std.common.traceability.test_query`). Unblock: the runner must first record
  those facts per attempt.
- `expired` has no `TestQueryStatus` variant; it parses as `Unknown` and is
  never PASS (TESTDB-008), which is safe but not a distinct typed outcome.

## Already recorded elsewhere

- `doc/08_tracking/bug/trace_app_text_option_fields_2026-11-15.md`
- `doc/08_tracking/bug/trace_cmds_no_passing_evidence_source_2026-11-15.md`
- `doc/08_tracking/bug/bug_closure_gate_wiring_remaining_2026-11-14.md`
  (CLI run evidence is `not_observed`)
- `doc/08_tracking/bug/workaround_retirement_bootstrap_advisory_hook_missing_2026-11-15.md`
- `doc/08_tracking/bug/mcp_progressive_hints_wiring_missing_2026-11-14.md`
  (hint resources/prompts, provider hooks, HINT-010)
- `doc/08_tracking/bug/goal_skill_routing_cli_and_read_receipts_2026-11-14.md`
- `doc/08_tracking/bug/2026-11-15_seed_tail_match_parse_int_wrong_value.md`
  (not reproduced)
- `doc/08_tracking/bug/2026-11-15_ctx_capture_truncation_windows_bounded_run_timeout.md`
