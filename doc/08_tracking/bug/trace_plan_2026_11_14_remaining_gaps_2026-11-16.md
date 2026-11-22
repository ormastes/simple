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

- `simple_ctx_purge` lost-write window is closed except one preemption gap
  (2026-11-18). `ctx_purge_commit` writes a temp file, then replays the tail:
  it re-reads the store, appends every row whose id it has not carried to the
  temp file, and loops (max 8 rounds, else StoreMoved with nothing deleted)
  until a read finds nothing new at an unchanged size, then renames. Replay
  dedupes on the full serialized row (ids come from an unlocked read-modify-write
  of `stats.sdn`, so two processes can share an id) and ignores an unterminated
  final segment (a torn row). Appenders
  (`_ctx_append_chunks_settled`) verify row presence by id after writing, not
  by byte size (the same-size false pass is gone), and re-apply if absent.
  Rows landing before the last read are replayed; rows landing after the
  rename are caught by the presence check. Still lost (honest): an append whose
  write AND presence check both fall between the purge's last stable read and
  its rename (`src/app/mcp/main_lazy_ctx_tools.spl`, the `file_rename` call in
  `ctx_purge_commit`); the writer then holds the old inode and sees its row
  present. Also pre-existing: two concurrent purges can resurrect rows the other
  dropped (each snapshots, the later rename wins). The presence check reads only
  the bytes written since the pre-write size (full read as fallback), so it is
  O(new bytes) per append. `std.io_runtime` offers only unconditional `file_rename` and the
  create-only `file_hardlink`; neither is a rename-if-unchanged. Unblock: an OS
  compare-and-rename (renameat2 RENAME_EXCHANGE then drain the old inode's
  tail). Specs: `test/01_unit/app/mcp/ctx_append_recheck_spec.spl`.

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
  `std.common.traceability.case_events`). Closed 2026-11-18: events now carry optional facts
  (`at_micros`, `failure`, `host`, `backend`), stored in the sidecar table
  `trace_case_event_facts` (the strict 9-column event table and legacy databases are untouched; old
  rows decode with every fact absent). `TestQueryRow` gains `started_at`, `duration` (finished minus
  started event time), `failure`, `host`, `backend` as typed newtypes/`Option`, shown by CLI, MCP and
  `explain`. Closed 2026-11-18 (second pass): `failure_code` (`TestFailureCode`: assertion, panic, timeout, unknown), `definition_digest` (sha256 of the spec file bytes, once per spec path per process) and `binary_digest` (sha256 of the recording process's executable (the recorder child, not the worker that ran the cases, resolved via `self_exe_path`; never argv[0]), once per process, absent when no real executable resolves) are in the same sidecar (columns widened in place for older databases), on `TestQueryRow`, and as three more cells after `failure` in CLI, MCP and `explain`. Digests are stamped by the parent runner at record time (`src/lib/nogc_sync_mut/test_runner/trace_digests.spl`), not by the child, because only the parent knows the spec path. `failure_code` is classified at the emission site from the failure message; the spec framework has no timeout or panic signal inside a finished event (a panic or timeout kills the child before a finished event exists), so those two values are produced only if the message says so and a crash is not representable (no event). Still absent: `artifact_refs`. Blocker: the runner has no per-case artifact path. The only artifact path is the per-spec-file result evidence file set at `src/app/test_runner_new/test_runner_single.spl:1716` (`SIMPLE_TEST_RESULT_FILE`), which is per spec file, not per case, and `TraceCaseEvent` has no field for it. Unblock: a case-level artifact registration API in the spec framework plus a retained artifact directory per run. `failure` is a clipped message summary. `level` of Windows backslash paths is recognised (char-loop
  normalisation; `replace` of a backslash misbehaves on the seed, and a spec literal with a
  backslash followed by a digit is lexed as an octal escape, so specs build such paths with `\`).
  **Open gap (recording path):** `simple test` exits 2 when `SIMPLE_TRACE_CASE_EVENTS=1`
  (`src/app/test_runner_new/test_runner_main.spl:1578-1583`, a deliberate fail-closed gate: frozen
  source bytes and effective options are not yet bound to preparation). Facts are therefore recorded
  only via the buildrunner path (`remote_test_runner_v1.spl`) or direct DB calls, not by a local
  `simple test`; I verified emission by calling `emit_trace_case_event` directly. The failure
  summary is clipped to 240 bytes on a character boundary.
  **Investigated 2026-11-22: the gate stays. Lifting it needs owner decisions, not just wiring.**
  Most pieces exist but are not connected to `simple test`: the option capture
  (`src/app/test_runner_new/trace_execution_config.spl`, `capture_trace_execution_configuration`),
  the SSpec planner with per-file source sha256 (`src/app/traceability/extract/sspec_run_request.spl`,
  `build_sspec_trace_request_single_owner`), the preparation transport
  (`src/app/test_runner_new/trace_preparation.spl`, `prepare_trace_sspec_run_via_db_lane`, whose header
  says "not yet connected to test dispatch"), and the reconciliation of events against the frozen plan
  (`update_test_database_from_record` with `trace_run_id`, reached through `test_db_lane_main.spl
  --trace-run=`). Emitted names (`spec.spl` `_execute_it`: `suite > context > leaf`) already match the
  planner's selector. The blocker: the capture can never be admitted. It always produces
  `timeout_binding: "per_file_unresolved"`, `cache_policy: "unresolved"` and at least six
  `unresolved_fields` (effective per-file timeout, slow-file adjustment, `@timeout` header directive,
  worker environment, feature-gate disposition, cache policy). `validate_trace_execution_configuration`
  (`src/lib/common/traceability/execution_config.spl:75`) rejects all three, and its binding wrapper
  `validate_trace_request_configuration` (`execution_config_binding.spl`) has no caller in `src/`. So no
  local run can produce an admissible `configuration_id` until the runner's execution semantics change.
  Owner decisions needed:
  (1) timeout: does one fixed trace timeout override `@timeout` directives and the slow-file
  adjustment, or does the schema bind a per-file timeout list?
  (2) cache: force the result cache off in trace mode (the validator requires `disabled`)?
  (3) worker environment: which env vars are the bound set (precedent: the allowlist at
  `remote_test_runner_v1.spl:122-130`)?
  (4) feature-gated specs: refuse in trace mode, or bind the disposition?
  (5) frozen bytes: the worker re-reads the spec from disk by path (`test_runner_single.spl`
  `spec_timeout_secs_directive`, compile). Should it execute an owned snapshot (needs path remapping
  and breaks relative imports), or re-hash before and after (detects change only and leaves a TOCTOU
  window)? Either way the import closure stays unfrozen.
  (6) specs with interpolated case names: the planner rejects them. Should trace mode refuse those
  specs outright?
  Steps once decided:
  (a) resolve those fields in `trace_execution_config.spl` under a trace-mode policy so the validator
  passes, and have runner dispatch enforce the captured config (timeout, cache off, worker env);
  (b) add a planning child mode, because the planner carries the compiler frontend and must stay out
  of the runner closure. It reads and hashes the selected files and builds the context
  (`configuration_id` from the capture, `binary_id` from the executable digest), then calls
  `prepare_trace_sspec_run_via_db_lane`;
  (c) apply the frozen-bytes choice from (5);
  (d) make `record_test_run_via_db_lane` pass `--trace-run=<run_id>`;
  (e) only then replace the unconditional gate with fail-closed checks on (a) through (d).
  Lifting the gate without (d) would record events against an unprepared fresh run. Today the gate is
  the only thing that prevents that.
- Bug-closure run evidence (plan 4.2/4.3), still blocked on the TestDB side. `bug_closure_evaluate_v1` takes `BugTestRunV1` rows (`case_id`, `backend`, `phase` PreFix/PostFix, `outcome`, `source` head) and the CLI (`src/app/bug_resolve/closure_cli.spl`) passes `runs: []` with `BugRunEvidenceV1.NotObserved`. `TestQueryRow` now supplies case, backend, outcome and the executable and spec digests, but still has no source snapshot (the git head a run was built from; `RunnerTestDb` records none, so "source-matched" cannot be judged) and no pre-fix/post-fix phase (a run is not tagged with whether it preceded the fix). A consumer that mapped rows to `BugTestRunV1` would have to invent both, so none was written. Unblock: record the source head on the run row at `start_run`, and let a closure request name the pre-fix and post-fix run ids.
- Perf (scoped query), closed 2026-11-18: `TestDatabaseExtended.get_trace_case_events_by_path(run_id)` decodes the table once per run and groups by path; `query_scoped_attempts` now decodes once per run instead of once per (run, path), and `get_trace_case_events` reuses it. Equality with the per-path read is pinned in `test_query_cli_spec.spl`.
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

### 2b. Public bare primitives across the wider trace surface (census 2026-11-18)

The §2 claim covers only the model structs. A field/param/return census over
src/lib/common/traceability, src/app/traceability, main_lazy_trace_tools,
main_lazy_ctx_tools, test_query_cli (fn params/returns on pub fn|me plus pub
struct/class fields typed bool/int/i*/u*/f*) found 168 findings. PR #10255 changed 30
fields (the codec limit families graph, declarations, document, qualification,
conventions: 28 `max_*` fields, plus the 2 `TraceCodecTextBudgetV1` limits) to
`TraceCountLimitV1` / `TraceByteLimitV1` (envelope_types_v1.spl); 140 remained.
32 of those were the `value` payload of single-field newtypes themselves (irreducible).

Follow-up 2026-11-18 (src/lib/common/traceability, excluding test_query.spl and
case_events.spl): the 72 non-newtype findings there are now 0. Bare bool flags became
two-variant enums (`TraceCompletenessV1`, `TraceAvailabilityV1`, `TraceChangeStateV1`,
`TraceRebuildScopeV1`, `TraceStageStateV1`, `TraceLookupOutcomeV1`, `TraceExecutionStateV1`,
`TraceSeedStateV1`, `TraceFailFastV1`, `TraceParallelismV1`, `TraceSelectionScopeV1`;
existing `TraceOverridePermissionV1`, `TraceCodecValidityV1`, `TracePageCompletenessV1`
reused); counts, positions and codes became `value` newtypes
(`TraceLineNumberV1`, `TraceColumnNumberV1`, `TraceByteOffsetV1`, `TraceUsedCountV1`,
`TraceCoverageCountV1`, `TraceAttemptNumberV1`, `TraceTimeoutSecsV1`, `TraceSeedV1`,
`TraceWorkerCountV1`, `TraceShardIndexV1`, `TraceShardCountV1`, `TraceEvaluationExitCodeV1`;
existing `TraceCountLimitV1`, `TraceGraphByteCountV1`, `TracePageLimitV1`,
`TraceResultCountV1` reused). The scanner now reports 28 findings in that scope, all `value`
payloads of single-field newtypes (15 before, 13 new newtypes). Whole-surface totals:
140 -> 81 remaining (45 irreducible `value` payloads, 36 non-newtype, all in src/app).
Remaining non-newtype findings by file (count):

- src/app/mcp/main_lazy_ctx_tools.spl: 14
- src/app/traceability/capture_v1.spl: 7
- src/app/traceability/snapshot/git_provider.spl: 3
- src/app/traceability/query_options_v1.spl: 3
- src/app/traceability/cli_options_v1.spl: 3
- src/app/traceability/extract/snapshot_partitions.spl: 2
- src/app/traceability/snapshot_preview.spl: 1
- src/app/traceability/snapshot/git_batch.spl: 1
- src/app/traceability/extract/snapshot_pipeline.spl: 1
- src/app/traceability/extract/snapshot_delta.spl: 1

Not yet scanned for param/return primitives in: ctx_*.spl, test_db_compat.spl,
test_extended/database.spl, trace_events.spl (0 field/fn hits in this census; the
checker only sees single-line signatures). main_lazy_ctx_tools.spl has 14 findings.

Batch 2026-11-19 (test_query, case_events, test_query_cli, main_lazy_trace_tools,
test_db_compat, trace_digests, trace_events, trace parts of test_extended/database):
census before = after = 0 on the `check-primitive-api-added` counter for all eight
files (the checker counts only `pub fn|me` lines; these files' trace API was already
newtyped). A wider scan (any `: bool|iN|uN|fN`, `-> bool|iN`, class methods without
`pub`) found the only trace-specific public primitive: `RunnerTestDb.trace_run_is_prepared
-> bool`, now `trace_run_prep_state -> TraceRunPrepState` (enum Prepared|Unprepared).
Remaining non-trace primitives, deliberately untouched (generic test-DB timing/count
API with wide caller sets): RunnerTestDb/TestDatabaseExtended `complete_run`
(test_count/passed/failed/timed_out), `cleanup_stale_runs`, `prune_runs`,
`record_timing_observation`/`promote_timing_baseline`/`prior_anomaly_warning -> bool`,
`test_count_by_status -> (i64 x4)`, resource-run ms/bytes params, `get_*_id -> i64?`;
plus private-by-convention `_trace_prepare_failed: bool`, private consts
(`*_LIMIT: i64`) and the one-field newtype `value: i64` payloads.

Batch test-DB API 2026-11-19: `RunnerTestDb` / `TestDatabaseExtended` public API no longer
carries bare primitives for the previously listed set. New std.database.test_extended types
(`types.spl`): `TestRunCount`, `TestRunAgeHours`, `TestRunKeepCount`, `TestRowId`,
`TestStageMs`, `TestDurationMs`, `TestByteCount`, `TestProcessCount`, `TestSignalNumber`,
`TestExitCode` (one-field `value:` newtypes), `TestAnomalyWarning` (Warned|Quiet),
`TestTimingOutcome` (Applied|Refused), and structs `TestStatusCounts`, `TestTimingStats`,
`TestCaseCounts` replacing tuples. Converted: `complete_run`, `cleanup_stale_runs`,
`prune_runs`, `record_timing_observation`, `promote_timing_baseline`,
`prior_anomaly_warning`, `test_count_by_status`, `record_resource_run`, `get_file_id` /
`get_suite_id` / `get_test_id` / `get_or_create_*`, and every `test_id`/`suite_id`/`file_id`
parameter (`TestRowId`), `get_test_timing`, `get_test_counts`. SDN wire format unchanged
(`.value` serialised exactly as before). Still bare (deferred, no caller-set change yet):
`update_test_result(duration_ms: f64)`, `update_timing`/`add_timing_run(duration_ms: f64,
baseline_eligible: bool)`, `record_baseline_generation(generation/p50/promoted_at)`,
`collect_timing_runs(max_count)`, `is_flaky_test -> bool`, `save() -> bool`, record
structs (`TimingSummary`, `TestInfo`, ...) pub fields, and `ResourceUsage`/`TestDbFileRow`
source fields wrapped at the call site.

Deferred test-DB batch 2026-11-22: the deferred set above is converted except the record
structs. New types: `TestBaselineGeneration`, `TestTimestamp` (`value: i64` newtypes),
`TestBaselineEligibility` (Eligible|Ineligible), `TestFlakiness` (Flaky|Stable),
`TestDbSaveOutcome` (Saved|Failed). `update_test_result`/`update_timing`/`add_timing_run`
take `TestDurationMs`; `add_timing_run` takes `TestBaselineEligibility`;
`record_baseline_generation` takes `TestBaselineGeneration`/`TestDurationMs`/`TestTimestamp`;
`collect_timing_runs[_for_cohort]` take `TestRunCount`; `is_flaky_test -> TestFlakiness`;
`TestDatabaseExtended.save -> TestDbSaveOutcome` (both test_db_compat wrappers compare it
explicitly). SDN unchanged (`baseline_eligible` still written as "true"/"false").
Still bare: pub fields of the record structs (`TimingSummary`, `TestInfo`, `TrdRunRecord`,
...), `ResourceUsage`/`TestDbFileRow` source fields.

Closed 2026-11-22: `promote_timing_baseline` could never return `Applied` after a single
observation because `update_test_result` refreshed timing stats (`update_timing`) before
recording the run (`add_timing_run`): the stats lagged one observation and a first run never
created its `timing` row. The two steps are swapped (as `record_timing_observation` already
did) and `test_extended_primitive_types_spec` pins `Applied` (old order: 5/6, fixed: 6/6).
