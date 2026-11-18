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
and the graph wire DTO `TraceGraphLocatorV1.locator_kind` are now the closed enum `TraceLocatorKind` (text only at the SDN boundary via
`locator_kind_name` / `parse_locator_kind`; unknown wire text is rejected `invalid_enum`).

## 3. MCP / ctx

- `simple_ctx_purge` lost-write window is narrowed, not closed. Appends now
  re-check the store size after writing (`_ctx_append_chunks_settled`,
  `src/app/mcp/main_lazy_ctx_tools.spl`), which catches a purge rename landing
  between an append's write and its re-check. Still lost: an append whose size
  read, write and re-check all land between `ctx_purge_commit`'s final key check
  and its rename; and a same-size false pass (a purge that shrinks the file by
  exactly the appended bytes). Unblock: an OS compare-and-rename, or the purge
  re-reading the store after its rename and replaying rows appended since its
  snapshot.

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
- `TESTDB-010` is implemented (2026-11-18): `simple test query|explain --bug <id>`,
  `--requirement <id>` and `--levels a,b` (`src/app/test_runner_new/test_query_cli.spl`) and the
  MCP `simple_test_query` fields `bug` / `requirement` / `levels`
  (`src/app/mcp/main_lazy_trace_tools.spl`) share one resolver,
  `src/app/traceability/test_query_scope_v1.spl`, feeding
  `RunnerTestDb.query_scoped_attempts`. Linkage uses data that already exists, no
  graph build: a bug resolves to its legacy bug-DB `reproducible_by` spec path
  (`legacy_bugs_v1.spl`), a requirement to the `# @req` headers
  (`annotations_v1.spl`) of the spec paths the TestDB has planned cases for (the
  test tree is ~21k specs, far over the 4096-file scan budget of
  `spec_annotations_v1.spl`, so it is not scanned). Remaining limits: a requirement
  is found only if a recorded run planned its spec; linkage is spec-file granular,
  not case granular (every recorded case of a linked spec is returned); plan 3.2
  acceptance item 2's "case definitions" and "executable/source identity" are not
  in the rows (see next item).
- Plan 3.5 return fields: `level` is now on `TestQueryRow` (`TestLevel`, derived from the
  `test/NN_<level>/` path), and rows carry `case_key`. Still absent because the runner
  records only `case_name`/`phase`/`outcome` per event (`TraceCaseEvent`,
  `std.common.traceability.case_events`): `test_definition_digest`, `binary_digest`,
  `host/backend`, `started_at`, `duration`, `failure_code`, `artifact_refs`. Unblock:
  the runner must first record those facts per attempt.
- Perf (scoped query): `query_scoped_attempts` (`src/lib/nogc_sync_mut/test_runner/test_db_compat.spl:337`) calls `get_trace_case_events` once per (run, path), and each call re-decodes the whole `trace_case_events` table (`src/lib/nogc_sync_mut/database/test_extended/database.spl:380`), so cost is runs x paths x table size. Fix needs a per-run grouped read on `TestDatabaseExtended` (decode once, group by path); not done here because it adds a new DB API.
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
