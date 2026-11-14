# Feature Expert — bug_closure_gate

Pure evaluator deciding whether a bug may move to a closed state (plan
`simple_traceability_spipe_bug_mcp_skills_improvement_plan_2026-11-14.md` §4, BUG-001..006).

## Read first
- Impl: `src/app/bug/closure_gate.spl` — `bug_closure_evaluate_v1(candidate, bug_id, policy, test_db_view, workaround_index) -> BugClosureReceiptV1`
- Spec: `test/01_unit/app/bug/bug_closure_gate_spec.spl` (9 scenarios)
- Workaround input type: `src/app/bug/workaround_index.spl` (`WorkaroundIndex`, reused as is)
- Remainder: `doc/08_tracking/bug/bug_closure_gate_wiring_remaining_2026-11-14.md`

## Contract
- Fix dispositions (Fixed, Closed) need: reproducer observed RED pre-fix (E-BUG-REPRO-001); distinct
  prevention case or exception reviewed by a non-author (E-BUG-PREVENT-002); post-fix Passed on
  EVERY required backend at the candidate head, Skipped/Cached/NotRun/stale never count, empty
  backend policy blocks (E-BUG-EVIDENCE-003); no live or unprovable workaround (E-BUG-WR-004);
  resolvable bug/case/requirement refs (E-BUG-LINK-005); unchanged bug_state/head/workaround
  revision (E-BUG-RACE-006).
- Non-fix (Triage, Duplicate, Invalid, Wontfix, Deferred) need no fix evidence, receipt kind
  `NonFixDisposition`, but link and race checks still apply.
- Pure: value inputs only, no I/O, no DB write. Caller transitions status only on `Allowed`.

## Non-negotiables
1. Do not weaken a check to make a bug closable; add evidence instead.
2. Keep the evaluator pure; wiring lives in the caller (not yet done).
3. Domain wrapper types for all new public ids; no raw text ids.
