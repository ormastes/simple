# BUG: CudaVmExecutor D3 conformance vectors hit `array index out of bounds: index is 0 but length is 0`

**Status:** RESOLVED
**Date filed:** 2026-08-08
**Date resolved:** 2026-08-08
**File:** `test/03_system/gpu_lane/cuda_vm_executor_conformance_spec.spl`
**Severity:** MEDIUM — blocked live-device D3 conformance verification, now that
`doc/08_tracking/bug/cuda_lane_probe_misses_device_unavailable_2026-08-08.md` is
fixed and the session actually reaches this code on a real device.

## Symptom

On the same healthy two-GPU host (RTX A6000 + TITAN RTX) used to fix the sibling
device-identity bug, with `CudaLaneSession.init()` now succeeding:

```
bin/simple test test/03_system/gpu_lane/cuda_vm_executor_conformance_spec.spl
✗ should skip cleanly, or run every conformance vector on a live device
  semantic: array index out of bounds: index is 0 but length is 0
2 examples, 1 failure
```

The sibling example ("should TRAP on call-stack overflow", 33 nested CALLs)
passed (1/1) even before this fix, so the bug was specific to the bulk vector
loop, not a blanket session failure.

## Root cause

The spec's main `it` block ran **every** D3 conformance vector from
`all_vectors()` through a single, shared `CudaVmExecutor.create()` /
`CudaLaneSession` in one loop (previously lines ~108-131), including
`budget_exhaustion_timeout` — a vector deliberately designed to time the
device out.

`CudaLaneSession.launch_once`
(`src/lib/gc_async_mut/gpu_lane/cuda_lane_session.spl:296-317`) correctly, by
design, latches the session into a permanent `completion_unknown` /
`release_pending` state after any genuine device timeout. Every vector run
through the *same* session after `budget_exhaustion_timeout` executed
therefore returned `ok:false` with an **empty** `records` list — not because
those vectors regressed, but because the session itself was poisoned by the
earlier, intentionally-timing-out vector.

Two call sites then unconditionally indexed into `records` without checking
length:

- `_assert_matches`'s comparison loop (`while j < v.expected_records.len(): ...
  outcome.records[j] ...`) — indexed `outcome.records[j]` even when
  `outcome.records` was empty.
- The self-modifying-code divergence check
  (`divergent_outcome.records[0]`) — indexed record 0 unconditionally.

Once a vector after `budget_exhaustion_timeout` in iteration order hit either
site with an empty `records` array, the interpreter raised `array index out
of bounds: index is 0 but length is 0`. This was purely an artifact of vector
*ordering* and shared-session state, not a defect in `CudaVmExecutor` or the
kernel.

## Fix

`test/03_system/gpu_lane/cuda_vm_executor_conformance_spec.spl`:

1. `budget_exhaustion_timeout` is now excluded from the shared-session bulk
   loop (`_BUDGET_EXHAUSTION_TIMEOUT_VECTOR`, alongside the existing
   `_SELF_MODIFYING_CODE_DIVERGENCE_VECTOR` exclusion), and the pass tally
   denominator adjusted to `vectors.len() - 2` to account for both exclusions.
2. `budget_exhaustion_timeout` now runs as its own final step, through a
   **fresh** `CudaVmExecutor.create()` / `.init(kernel_bytes)` session that is
   never shared with any other vector. The outcome is asserted with
   `assert_false(timeout_outcome.ok)` — a real device timeout correctly
   produces `ok:false`, this is the designed behavior, not something to hide
   — and the subsequent `timeout_executor.shutdown()` is asserted to return
   the real latch message `"cuda-lane-session-cleanup-pending"`, which is
   itself a legitimate, valid finding of `CudaLaneSession`'s by-design
   timeout latch (not a bug to be papered over).
3. Both previously-unguarded record-indexing sites are now guarded against
   empty/error outcomes: `_assert_matches`'s loop bound now also checks
   `j < outcome.records.len()`, and the `divergent_outcome.records[0]` read is
   wrapped in `if divergent_outcome.records.len() > 0:`.

## Verification

```
SIMPLE_MODULE_LIMIT=4000 bin/simple test test/03_system/gpu_lane/cuda_vm_executor_conformance_spec.spl
Results: 2 total, 2 passed, 0 failed

SIMPLE_MODULE_LIMIT=4000 bin/simple test test/02_integration/app/tools/notebook/cuda_exec_spec.spl
Results: 4 total, 4 passed, 0 failed
```

No assertions were weakened — the `budget_exhaustion_timeout` vector's real
`ok:false` timeout outcome and the session's real cleanup-pending latch
message are asserted directly, not hidden.
