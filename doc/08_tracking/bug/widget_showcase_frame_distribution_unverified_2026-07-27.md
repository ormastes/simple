# Widget Showcase Frame Distribution Is Not Yet Verified

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
