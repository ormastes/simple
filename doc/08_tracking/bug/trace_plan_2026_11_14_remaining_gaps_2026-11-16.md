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

Closed-set `text` fields that could become enums if the exemption is ever
narrowed: `TraceLocator.locator_kind` (file, symbol, scenario, section, cas;
about 30 string-compare sites, including `graph_schema_v1.spl` and
`graph_wire_v1.spl`) and `TraceDiagnostic.severity` (error, warning).

## 4. Test query and harness

- The plan (sections 3.5, 9.1) lists `TESTDB-001`..`TESTDB-010` as one range and
  defines no per-id rows. Specs now use the mapping in
  `test_query_spec.spl` (001 exact query, 002 result variants, 003 provenance and
  missing identity, 004 pagination/rejected/failed queries); 005..010 and an id
  for read-only/no-write isolation remain undefined by the plan.

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
