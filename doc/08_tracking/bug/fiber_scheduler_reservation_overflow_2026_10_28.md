# Fiber scheduler reservation overflow

Status: fixed in the accompanying source change; focused Phase 1 verification passed.

The scheduler checked admission using `reserved + estimate <= budget`. At the
maximum i64 budget that addition can wrap, admitting work beyond the budget and
corrupting reservation accounting. The forced-progress path can likewise exceed
the representable reservation total when an admitted fiber is parked.

The fix compares the estimate to remaining budget without adding, checks the
forced-progress addition against the i64 maximum, and latches the existing
scheduler error field while leaving the pending head and reservations intact.
Already admitted work can still wake and complete. FileFiber counts queued
fills and ready async results as external work, drains runnable/external work,
then reports a scheduler error and terminalizes unfinished fibers. It also
handles invalid scheduler configuration before entering the host loop.

## Executable evidence

- Exact regression: `test/01_unit/lib/common/task_runner/fiber_scheduler_spec.spl`,
  "does not wrap the fit check at the maximum i64 budget". Prior baseline run
  failed with expected pending count 1, actual 0 (`/tmp/fiber-scheduler-red.log`).
- Generalization: the same spec's "fails closed when progress would overflow
  parked reservations" and "does not mistake an over-budget reservation for
  ordinary budget headroom" cover forced admission and legitimate overcommit.
- Carrier regressions: `test/01_unit/compiler/driver/file_fiber_v1_spec.spl`,
  invalid-worker termination, overflow terminalization with queued-work draining,
  and queued-fill suppression of forced admission.

Final focused run on 2026-10-28 used the existing aa58a24e Phase 1 generation in
`/Users/ormastes/wt/release-bootstrap-integration-20261025`, with `SIMPLE_LIB`
pointing at this worktree's `src`, and `test <spec> --mode=interpreter --assert-ran`.
Scheduler: 14 declared/executed/passed; carrier: 12 declared/executed/passed;
zero failures, skips, or dropped examples. Logs: `/tmp/scheduler-resume-core.log`
and `/tmp/scheduler-resume-carrier.log`. No Phase 2 rebuild was performed.

## Descriptor scope

Overflow is raised only when no fiber is runnable and no external operation
can wake one. Normal FileFiber OPEN/READ ownership is protected by in-flight IO
or a runnable completion; the close is submitted before parsing/dependency
parks, and is drained as external IO. The existing read-submit/close-submit
failure descriptor leaks are separate from this overflow change. This change
does not claim to fix them. An earlier unverified fd cleanup proposal is
preserved outside the worktree at `/tmp/scheduler-resume-preserve.patch`.
