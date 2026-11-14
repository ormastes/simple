# bug closure gate: wiring and BUG-007..012 not done (2026-11-14)

Done: pure evaluator `src/app/bug/closure_gate.spl` (BUG-001..006), spec
`test/01_unit/app/bug/bug_closure_gate_spec.spl`.

Remaining (unblock: evaluator merged, then a wiring slice):
- Call `bug_closure_evaluate_v1` from `src/app/bug_resolve/main.spl` behind feature flag
  `bug.closure_gate`; build the candidate/view from the tracking DB (not done; evaluator takes values only).
- CLI `bug closure-check <bug_id>` printing the receipt codes and proofs.
- BUG-007..012 rows of plan section 9.
- `BugStatus` is unchanged; mapping Allowed receipts to statuses is part of the wiring.
- `workaround_query.spl` unchanged; callers must supply a `WorkaroundIndex` at the candidate head.
