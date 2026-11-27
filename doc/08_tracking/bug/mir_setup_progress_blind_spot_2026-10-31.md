# MIR setup progress blind spot

**Status:** bounded progress checkpoints added; integration evidence UNRUN.

## Problem

The native build reported MIR progress at `0/N` before `lower_to_mir`, then
could spend substantial time preparing the entire MIR schedule before the first
module completed. The existing `[mir-slow]` record is emitted only after a
module returns. That left preloop setup indistinguishable from a slow first
module. The observed long-running build does not establish a hang or prove
which setup operation dominates.

## Change

`driver_pipeline_lowering.spl` now emits up to eight `log_build_progress`
records for warm names, archive lookup, provider feed, physical ownership,
struct prescan, enum inventory, composite inventory, and first-module entry.
Each record reports `phase=mir`, `unit_kind=modules`, `done=0`, task position
4/6, zero failures/cache hits, and an existing HIR or scheduled-physical total.
The markers do not count setup work as completed modules or change lowering,
ownership, cache admission, or failure decisions.

## Regression evidence and pending test dependency

The telemetry source was reviewed structurally. Native execution is **UNRUN**;
no compiler build was launched for this change. Planned integration oracles
require ordered setup rows, real MIR completion, a runnable record/enum fixture,
and an intentionally unresolved external symbol with no successful link or
accepted output artifact.

The draft scenarios are not included in this source-only change. Review found
that the existing `test_compiled_child_run_v1` uses the V3 pinned child provider,
which starts in `/` with a sealed environment including `PATH=/nonexistent`.
Parent no-stub/no-delegate flags therefore do not reach the compiler child.
These drafts cannot establish the planned compiler assertions through that route.
A separate test-support change must use the existing configured V4 provider,
explicit pinned compiler/runtime/tool environment and cwd, supported descendant
containment, and complete bounded collection/cleanup receipts. No V3 semantics
or runtime authority may be weakened to enable the tests.

The known whole-closure provider-rebuild cost remains a hypothesis for future
profiling, not a causal finding from these progress markers.
