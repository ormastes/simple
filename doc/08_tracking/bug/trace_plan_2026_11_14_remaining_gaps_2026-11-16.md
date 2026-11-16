# Traceability / bug / MCP / skills plan 2026-11-14 — remaining gaps after waves 1–3

Date: 2026-11-16. Release line: `release/1.0.0`.
Plan: `simple_traceability_spipe_bug_mcp_skills_improvement_plan_2026-11-14.md`.

This record collects the open items that have no other bug record. Items that
already have their own record are listed at the end by path only.

## 1. `trace missing` exits 1 on an incomplete graph; the plan says 2

- `src/app/traceability/query_main.spl:35` documents
  `0 rendered, 1 incomplete or not found, 2 invalid`.
- Plan §6.4 and the newer subcommands (`matrix`, `links`, `explain`, `diff`,
  `report`, via `trace_command_verdict_v1` in
  `src/lib/common/traceability/query_status_v1.spl`) and the MCP
  `simple_trace` tool all report an incomplete graph as exit 2.
- Unblock: route `trace missing` through `trace_command_verdict_v1`, update
  `trace_node_query_spec` expectations, and check CLI callers that test for 1.

## 2. Public primitives still left in the traceability model

The `primitive_api` lint checks `pub fn` signatures only, so these are not
flagged, but they break the "no primitive in public API" requirement:

- `src/lib/common/traceability/model.spl` struct id/count fields still bare
  `text`/`i64`: `TraceQuery`, `TraceLocator`, `TraceClaim`, `TracePolicy`,
  `TraceEdge`, `SnapshotSubject`, `TraceDiagnostic`, `TraceNode`
  (converted so far: `TraceEdgeOrigin`, `TraceQueryResult`, `TraceAuthority`,
  `TraceDocument`, `TraceConventionRule`, `TraceOrigin`).
- `TraceReverseIndexV1.by_key` is `Dict<text, [TraceEntityIdV1]>`.
- Unblock: convert one struct per change, smallest use-site count first,
  unwrap at use sites, keep the SDN wire format byte-identical (codec specs).

## 3. MCP / ctx

- `src/app/mcp/main_lazy_ctx_tools.spl` keeps 12 `primitive_api` findings and
  23 lint errors (unchanged by waves 1–3).
- `simple_ctx_purge` takes no lock; an append racing an applied purge can be
  lost (documented in `doc/07_guide/app/mcp/mcp.md`).
- Postings are rebuilt per store generation and only after 128 cache hits;
  there is no incremental update on append.
- `simple_trace` validates `profile` but does not change enforcement by it, and
  exposes only `operation: missing`.
- `simple_test_query`: the TestDB-absent (no cold start) path has no spec.

## 4. Test query and harness

- `simple test query` spec rows use `@req TESTDB-011..016`, ids chosen by the
  implementer; reconcile with the plan's TESTDB table.
- `--cursor` is a plain row offset, not an opaque token.

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
