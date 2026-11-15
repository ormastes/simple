# Feature Expert — bug_closure_gate

Evaluator deciding whether a bug may move to a closed state (plan
`simple_traceability_spipe_bug_mcp_skills_improvement_plan_2026-11-14.md` §4, BUG-001..006),
now wired into `bug-resolve` and the read-only `bug-closure-check` CLI.

## Read first
- Pure evaluator: `src/app/bug/closure_gate.spl` — `bug_closure_evaluate_v1(candidate, bug_id, policy, test_db_view, workaround_index) -> BugClosureReceiptV1`
- CLI adapter (reads, never writes): `src/app/bug_resolve/closure_cli.spl` — builds the typed inputs, calls the evaluator, renders the receipt
- Callers: `src/app/bug_resolve/main.spl` (`bug-resolve`), `src/app/bug_closure_check/main.spl` (`bug-closure-check --id=<id>`, exit 0 allowed / 1 blocked / 2 usage, never writes)
- CU-015 argument gate (kept, flags unchanged): `src/lib/nogc_sync_mut/database/bug_close_gate.spl` via `src/app/bug_resolve/close_gate.spl`
- Specs: `test/01_unit/app/bug/bug_closure_gate_spec.spl`, `test/02_integration/app/bug_closure_wiring_spec.spl`, `test/02_integration/app/bug_add_resolve_log_modes_spec.spl`
- Remainder: `doc/08_tracking/bug/bug_closure_gate_wiring_remaining_2026-11-14.md`

## Decision path (one source of the verdict)
1. `bug-resolve` validates token receipt fields (unchanged).
2. `bug_closure_argument_problem_v1`: for a fix disposition this IS the CU-015 `bug_close_gate`
   (spec path shape, `_spec.spl`, distinct, exist) so `--reproducer=` / `--prevention=` messages
   are unchanged; for a non-fix disposition it requires `--rationale=`. Argument validation only.
3. `bug_closure_cli_evaluate` -> `bug_closure_evaluate_v1`. The E-BUG-* codes and receipt are the
   only verdict. Nothing is written before the receipt is Allowed; a blocked close leaves the DB
   byte-identical (pinned in `bug_closure_wiring_spec`).
4. Only then `bug-resolve` logs, records token usage and resolves.

## Run evidence is NOT observed yet
The CLI has no TestDB run source, so the policy is `BugRunEvidenceV1.NotObserved`: pre-fix RED and
post-fix GREEN are not judged, and the receipt and the DB log say `run_evidence=not_observed`.
Workaround, broken-link and snapshot-race checks are fully live. `Observed` (the default for the
pure unit spec) judges runs as before. Do not describe a CLI close as test-verified.

## CLI flags added to bug-resolve
`--disposition=<fixed|closed|triage|duplicate|invalid|wontfix|deferred>` (default fixed),
`--rationale=<text>` (required for non-fix; logged as `not_a_verified_fix`),
`--source-head=<rev>` (default `git rev-parse HEAD`; must equal the workaround index revision).

## Contract
- Fix dispositions (Fixed, Closed) need: reproducer observed RED pre-fix (E-BUG-REPRO-001, only
  when run evidence is Observed); distinct prevention case or exception reviewed by a non-author
  (E-BUG-PREVENT-002); post-fix Passed on EVERY required backend at the candidate head
  (E-BUG-EVIDENCE-003, only when Observed); no live or unprovable workaround (E-BUG-WR-004, an
  absent/incomplete index also blocks); resolvable refs (E-BUG-LINK-005); unchanged
  bug_state/head/workaround revision (E-BUG-RACE-006).
- Non-fix dispositions need no fix evidence, receipt kind `NonFixDisposition`; link and race checks
  still apply. `bug_closure_disposition_kind_v1` is an exhaustive match (no wildcard arm).

## Non-negotiables
1. Do not weaken a check to make a bug closable; add evidence instead.
2. Keep the evaluator pure; all I/O lives in `closure_cli.spl`.
3. Domain wrapper types for all new public ids; no raw text ids.
4. Update the integration spec fixtures (spec files, workaround index at the pinned head) rather than the gate.
