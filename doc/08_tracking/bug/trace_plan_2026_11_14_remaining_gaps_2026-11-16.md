# Traceability / bug / MCP / skills plan 2026-11-14 — remaining gaps after waves 1–3

Date: 2026-11-16. Release line: `release/1.0.0`.
Plan: `simple_traceability_spipe_bug_mcp_skills_improvement_plan_2026-11-14.md`.

This record collects the open items that have no other bug record. Items that
already have their own record are listed at the end by path only.

## 2. Public primitives still left in the traceability model

The `primitive_api` lint checks `pub fn` signatures only, so these are not
flagged, but they break the "no primitive in public API" requirement:

- `src/lib/common/traceability/model.spl` struct id/count fields still bare
  `text`/`i64`: `TraceLocator` (about 110 field-use sites in src+test, measured
  2026-11-17, over the per-struct ceiling), `TraceClaim`, `TraceEdge`,
  `SnapshotSubject`, `TraceDiagnostic`, `TraceNode`. Needs new wrappers for
  blob ids and locator kinds (closed set: file, line, sdn-node, ...).
  Converted so far: `TraceEdgeOrigin`, `TraceQueryResult`, `TraceAuthority`,
  `TraceDocument`, `TraceConventionRule`, `TraceOrigin`, `TraceQuery`,
  `TracePolicy`.
- `TraceReverseIndexV1.by_key` is `Dict<text, [TraceEntityIdV1]>`.
- Unblock: convert one struct per change, smallest use-site count first,
  unwrap at use sites, keep the SDN wire format byte-identical (codec specs).

## 3. MCP / ctx

- `simple_ctx_purge` is a compare-and-swap on the store generation key, but an
  append that lands between the final key check and the rename still targets
  the replaced file and is lost (`src/app/mcp/main_lazy_ctx_tools.spl`,
  `ctx_purge_commit`). Unblock: an OS compare-and-rename, or appends that
  re-check the generation after writing.
- `simple_trace` validates `profile` but does not change enforcement by it, and
  exposes only `operation: missing`.
- `simple_test_query`: the TestDB-absent (no cold start) path has no spec.

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
