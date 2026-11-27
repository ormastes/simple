# bug closure gate: wiring partly done, remaining items (updated 2026-11-15)

Done:
- Pure evaluator `src/app/bug/closure_gate.spl` (BUG-001..006) and its spec.
- `bug-resolve` now decides through `bug_closure_evaluate_v1` via `src/app/bug_resolve/closure_cli.spl`;
  CU-015 (`bug_close_gate`) remains only as argument/existence validation with unchanged flags and messages.
  A blocked close writes nothing (byte-identical DB asserted in `test/02_integration/app/bug_closure_wiring_spec.spl`).
- Read-only `bug-closure-check --id=<id>` (exit 0/1/2) registered in `command_registry.spl`,
  `_CliMain/main_and_help.spl`, `bootstrap_check.spl`.
- `--disposition` / `--rationale` / `--source-head` on `bug-resolve`; non-fix dispositions close without fix evidence
  and are logged `not_a_verified_fix`.
- `bug_closure_disposition_kind_v1` is an exhaustive match.

Remaining (not done):
- Run evidence: the CLI uses `BugRunEvidenceV1.NotObserved` because there is no TestDB view provider
  (pre-fix RED, post-fix GREEN per backend are not judged at the CLI; E-BUG-REPRO-001 "pre_fix_red" and
  E-BUG-EVIDENCE-003 cannot fire there). Investigated 2026-11-16 (trace-side adapter in
  `doc/08_tracking/bug/trace_cmds_no_passing_evidence_source_2026-11-15.md`): NOT buildable from today's TestDB, no
  `BugTestRunV1` reader was added. Missing fields:
  - backend: `BugTestRunV1.backend` is a free-text `BackendIdV1`; no TestDB row, plan or event carries one. It would be written by
    the planner (`src/app/traceability/extract/sspec_run_request.spl:141`, `TracePlannedCase`, plus `TraceRunPlan` in
    `src/lib/common/traceability/run_plan.spl:14`) and persisted with the case events
    (`src/lib/nogc_sync_mut/database/test_extended/database.spl:336`, `record_trace_case_events` columns). `lane_id`
    is a runner lane, not a backend; do not map it by guesswork.
  - pre-fix vs post-fix phase: no field; a later run cannot prove an earlier RED. It would be a phase marker on the plan at
    `run_plan.spl:14`, written when the run is frozen.
  - bug case -> test case link, and candidate-head snapshot: only `TraceRunPlan.subject_id` exists, and only for plan-bound runs;
    the repo DB has no `trace_run_plans`/`trace_case_events` rows at all (confirmed).
  Unblock: the three fields above recorded by a plan-freezing runner lane, then a reader producing `BugTestDbViewV1.runs` and a
  distinct policy value (enum, not bool) for post-fix-only observation, with a receipt stating which checks were observed.
- Feature flag `bug.closure_gate` was not added: the gate is unconditional in `bug-resolve`.
- Non-fix dispositions still transition through `BugDatabase.resolve_bug` (status `Closed`); a distinct
  `Wontfix`/`Deferred` status transition needs a `BugDatabase` API (`src/lib/nogc_sync_mut/database/bug.spl`).
- `bug show --workarounds` (plan §5.3) not implemented.
- `bug retire-workaround` transaction is not wired into bootstrap; `bug resolve --auto-retire --evidence=<receipt-id>` absent.
- `check-dbs` bypass detection (direct SDN edit / external close must be caught, plan §4.3) not implemented.
- BUG-007..012 rows of plan section 9 are not covered by any spec.
- `src/app/cli/check_dbs.spl` (landed in 3bef089a210) calls `workaround_revert_candidates(index, db)` with two
  arguments while `src/app/bug/workaround_revert.spl` declares a third `today` parameter; not touched here.
- `BugStatus` is unchanged; requirement ids are not passed to the evaluator (`requirements: []`).

[Update 2026-11-23 `work/primitive-fix-20261122`]
- Run evidence CLI wiring (Items 2b/2c) implemented in `src/app/bug/closure_testdb.spl`,
  `src/app/bug_resolve/closure_cli.spl`, `src/app/bug_resolve/main.spl`, and
  `src/app/bug_closure_check/main.spl` (`5dd48e69674`): closure requests can now supply
  pre-fix and post-fix TestDB run IDs carrying `run_source_revision`, mapping observed runs into
  `BugTestRunV1` for `bug_closure_evaluate_v1`. Verified in `bug_closure_testdb_spec` (5/5),
  `bug_closure_wiring_spec` (8/8), `bug_closure_gate_spec` (11/11),
  `bug_add_resolve_log_modes_spec` (12/12), and `bug_resolve_cli_spec` (4/4).
- All other remaining items above (feature flag, `BugStatus` variants, `bug show --workarounds`,
  `retire-workaround` wiring, bypass detection, BUG-007..012, `check_dbs.spl` arity,
  `requirements: []`) and the Item 1 exit-2 trace gate (`SIMPLE_TRACE_CASE_EVENTS=1`) remain open/gated.
