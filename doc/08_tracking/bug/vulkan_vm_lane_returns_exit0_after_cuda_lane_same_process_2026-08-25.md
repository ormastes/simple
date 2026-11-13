# VulkanVmExecutor returns ok=true / exit=0 / 0 records when run after a CUDA lane in the same process (2026-08-25)
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** OPEN — `examples/08_gpu/backends/backends_spec.spl` is deliberately RED on this host
(`Results: 4 total, 3 passed, 1 failed, 1 skipped`), per the "correct spec that fails" rule.
**Binary:** Rust seed. **Host:** Linux, 2x NVIDIA, Vulkan 1.4.312 live.

## Evidence
Same program `PUSHI 1\nPUSHI 9\nSYS_RESULT\nPUSHI 3\nSYS_EXIT`, same `VulkanVmExecutor.create()` +
`init(svmg_vulkan_kernel.spv)` + `run_source(.., 1000, 0)`:

| process content | outcome |
|---|---|
| Vulkan case alone (scratch spec, `bin/simple test`) | `ok=true exit=3 records=1` (value 9) |
| `test/03_system/gpu_lane/vulkan_vm_executor_conformance_spec.spl` (Vulkan only) | `2 total, 2 passed` |
| `backends_spec.spl`: CUDA case (live, `exit=3`, 1 record) **then** Vulkan case | Vulkan: `ok=true`, **`exit=0`, `records.len()=0`** — `assert_equal failed: expected 3, got 0` |

`ok=true` with no sentinel and no records means the dispatch "succeeded" without the program's
effects reaching the mailbox — i.e. a silent wrong answer, not a skip. Every existing gpu_lane
conformance spec is single-backend per process, so this interference has no coverage today.

## Suspects
- Shared per-process state between `CudaLaneSession` / `VulkanLaneSession` — the GMB-1 mailbox
  arena or its sentinel/reader cursor (`std.nogc_sync_mut.test_runner.gpu_mailbox`), consumed by
  the first lane and not re-armed for the second.
- `vulkan_sffi_shutdown_reaped()` / CUDA context teardown ordering in the lane sessions.

## Unblock
Either fix the shared state so both lanes run in one process, or make the second lane FAIL
loudly (never `ok=true exit=0`). Keep `backends_spec.spl` strict; it goes green when fixed.
Related (different symptom, same area):
`doc/08_tracking/bug/vulkan_instance_init_fails_under_run_but_not_test_2026-08-25.md`.


## 2026-11-12 fix attempt — lane fix-runpath-gpu-20261112 (investigated, no in-scope fix)

Located the shared state named in the suspects: the GMB-1 mailbox arena and
its sentinel/reader cursor live in
`src/lib/common/svmg/mailbox_const.spl` / `src/lib/common/svmg/ref_vm.spl`
and are consumed by the lane executors in
`src/lib/gc_async_mut/gpu_lane/` (`cuda_vm_executor.spl`,
`vulkan_vm_executor.spl`, `cuda_lane_session.spl`,
`vulkan_lane_session.spl`) plus `std.nogc_sync_mut.test_runner.gpu_mailbox`.
The re-arm/teardown-ordering fix ("either fix the shared state so both
lanes run in one process, or make the second lane FAIL loudly") belongs in
those files. This lane's touch scope covers only
`src/lib/nogc_sync_mut/gpu/vulkan_vm/**`, which does not exist in the tree
(the executor is under `gc_async_mut/gpu_lane`) — so the fix site is out of
scope and no fake change was made.

Also noted: on current HEAD the hosted `vulkan_vm` lane
(`_run_vulkan_vm_lane` in `test_executor_hosted_lanes.spl`) runs a canned
`HALT 7` program per process and never runs CUDA and Vulkan lanes in one
process, so the interference still has no coverage — matching this
record's observation.

Recommended reassignment: a lane owning `src/lib/gc_async_mut/gpu_lane/**`
(and, if the fail-loud half is chosen, `src/lib/common/svmg/**`), with a
two-backend same-process conformance spec kept strict per the Unblock
section.

Verification pending: `examples/08_gpu/backends/backends_spec.spl` going
green (4 passed) on a 2x-NVIDIA Vulkan 1.4 host.

Status: OPEN (suspects confirmed in source; fix site out of lane scope).


## Triage 2026-11-13 (lane p3-async-20261113, base 80a8116e5e2) — not reproducible on this lane (host-bound)

This lane runs a Windows host with the tracked seed; the recorded
interference requires a Linux host with 2x NVIDIA, live Vulkan 1.4.312 and a
live CUDA lane in one process — none of which this lane can construct, and
`backends_spec.spl` cannot run meaningfully here. No fresh reproduction was
attempted; the evidence and suspects in the record body stand (shared
per-process GMB-1 mailbox arena / sentinel-reader cursor consumed by the
first lane; Vulkan/CUDA teardown ordering). The unblock condition is
unchanged: fix the shared state so both lanes run in one process, or make the
second lane fail loudly (never `ok=true exit=0`), keeping
`backends_spec.spl` strict. Routed to the GPU-lane owner. No source change.

## 2026-11-13 — fail-loud half landed (lane uia); row stays OPEN

Concrete fail-open matching the filed shape (`ok=true, exit=0, records=[]`):
`VulkanVmExecutor.run_source_persisting_data` returned `ok: not forced_timeout`
for a failed `dispatch_once`, so every dispatch error that is not a forced
timeout (`vulkan-lane-session-unavailable`, `-fenced-submit-unavailable`,
`-descriptor-create-failed`, `-command-record-failed`) read as a clean exit 0
with no records. It now returns `ok: false` with the session error
(`svmg_dispatch_error_outcome`, `src/lib/gc_async_mut/gpu_lane/vulkan_vm_executor.spl`).

Evidence, release/1.0.0 `35144b7f5e9` + this change, Linux aarch64 (DGX Spark
GB10), Rust seed sha256 prefix `af717f53d6bce3e5`:

- `test/02_integration/gpu_lane/vulkan_vm_executor_dispatch_error_spec.spl`:
  1/2 before the fix (`expected true to equal false`), 2/2 after.
- `test/03_system/gpu_lane/vulkan_vm_executor_conformance_spec.spl`: 2/2.
- `examples/08_gpu/backends/backends_spec.spl`: 4 examples, 1 failure — and it
  is not this record's shape. The **vulkan** example passes after the cuda
  example ran in the same process; the **cuda** example fails with
  `semantic: array index out of bounds: index is 0 but length is 0`
  (`o.records[0]`, no records from the CUDA lane on this host).

Not established: whether the original Vulkan-after-CUDA interference still
exists. It did not reproduce here, but the CUDA example did not complete
cleanly on this host, so the precondition (a clean live CUDA run first) was not
met. The second fail-open candidate (dispatch succeeds, kernel writes no
sentinel, `_decode_sentinel` falls through to `ok: true`) was left alone: the
DBG-1 break/resume path may legitimately return a non-exit sentinel.

