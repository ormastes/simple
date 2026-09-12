# Widget Showcase Frame Distribution Is Not Yet Verified

**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

## Problem

The retained 4K/8K wrapper reported p50 and p95 by copying the arithmetic
mean. Those rows were not distribution evidence.

## Current Fix

- The showcase performs 12 warmup presents.
- It records each of the 200 measured present durations.
- It computes and emits real p50/p95 values plus sample and warmup counts.
- The wrapper fails closed unless the sample count equals the requested frame
  count, warmup is positive, and p95 is not below p50.
- The aggregate completion gate requires the same counts.

## Remaining Verification

1. In a fresh session, run
   `test/03_system/check/widget_showcase_perf_wrapper_spec.spl` once with an
   accepted source-matched pure-Simple runner and retain named failure output.
2. Generate the SSpec manual only after that focused run passes.
3. Run real native 4K and 8K probes on a qualifying Vulkan host and retain both
   `status.env` rows, logs, timing logs, readback checksums, RSS, and source
   provenance.

The latest diagnostic run was capped at 7/9 after three cycles. It is not a
performance qualification, and no 4K/8K FPS claim is valid yet.

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule C: filed before 2026-07-29, no runnable repro in the record, no status line existed); closed as stale per the "too old / not valid -> close" triage policy. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification if reopened.
