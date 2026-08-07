# Generic GPU-lane runner routing is not wired to the real B2/C2 executors

**Filed:** 2026-08-07, during Task E2 (`doc/03_plan/agent_tasks/gpu_remote_interpreter_parallel_plan_2026-08-07.md`)
**Status:** OPEN
**Severity:** Medium — no test currently claims otherwise, but the gap is
easy to miss because the real executors DO exist.

## Summary

`std.test_runner.gpu_lane_common.route_gpu_lane` (`src/lib/nogc_sync_mut/test_runner/gpu_lane_common.spl:100-123`),
the function the composite test runner's generic `remote(cuda(...))` /
`remote(vulkan(...))` dispatch (A3, `run_test_file_gpu_lane`) calls, still
unconditionally returns:

```
"{remote_backend} lane executor not yet implemented (see B2/B3/C2/C3)"
```

(a `FAIL`, not `skip:`) whenever the backend's driver/ICD is present and its
probed `rt_*` symbols resolve — this was correct when A3 landed (before
B2/C2 existed), but B2 (`CudaJitLaneExecutor`), C2 (`VulkanJitLaneExecutor`),
B3/B4 (`CudaVmExecutor`/`ResidentSession`), and C3 (`VulkanVmExecutor`) have
all since landed as real, independently-verified `GpuLaneExecutor`
implementations (see `doc/00_llm_process/feature_expert/gpu_remote_lanes/skill.md`).
`route_gpu_lane` was never updated to dispatch a spec file through one of
them — it has no knowledge any of them exist.

## Evidence

On this host (2 real NVIDIA GPUs, both CUDA driver and Vulkan ICD present):

```
$ command -v nvidia-smi && nvidia-smi -L   # succeeds, 2 GPUs listed
$ command -v vulkaninfo && vulkaninfo --summary   # succeeds
```

All 4 symbols `gpu_required_symbols` probes (`rt_cuda_init`,
`rt_cuda_module_load_data_bytes`, `rt_vulkan_alloc_buffer`,
`rt_vulkan_begin_compute`) resolve on the deployed binary (confirmed via the
same probe technique `gpu_lane_common.probe_gpu_symbol` uses — a throwaway
`extern fn <sym>() -> i64` probe file, checked for the absence of "unknown
extern function: <sym>" in the output).

So on this host, `route_gpu_lane(..., driver_present: true, missing_symbol: "")`
for EITHER backend returns the generic FAIL, not `skip:` — even for
`cuda_jit`/`vulkan_jit`, which have real, independently-passing executors
(`test/03_system/gpu_lane/cuda_jit_hello_spec.spl`,
`test/03_system/gpu_lane/vulkan_jit_hello_spec.spl`). Confirmed via
`test/03_system/gpu_lane/gpu_lane_matrix_status_spec.spl`'s host-aware
`slow_it` block (informational only — it does not assert a specific verdict,
only that the result is well-formed, for exactly this reason).

## Impact

A test author who writes a spec targeting `jit(remote(cuda(sm80)))` and
routes it through the generic composite-runner dispatch path (rather than
calling `CudaJitLaneExecutor` directly, as the existing B2/C2 specs do) gets
a hard FAIL on a host with real GPU hardware, even though a working executor
exists. Not a correctness bug in the executors themselves — a missing wiring
step in the generic dispatch layer.

## Fix sketch (out of scope for E2)

Extend `route_gpu_lane` (or a wrapper it delegates to) to recognize
`{cuda_jit, cuda_vm, cuda_vm_resident, vulkan_jit, vulkan_vm}` by parsed
spec-string shape (A1's extractors already produce backend/submode/target)
and, when driver+symbols are ready, actually construct and drive the
matching `GpuLaneExecutor` (`CudaJitLaneExecutor` / `CudaVmExecutor` /
`ResidentSession` / `VulkanJitLaneExecutor` / `VulkanVmExecutor`) instead of
returning the static "not yet implemented" message. `cuda_vm` additionally
has no in-tree system spec driving the D3 conformance table yet (separate,
pre-existing gap — see `doc/00_llm_process/feature_expert/gpu_remote_lanes/skill.md`'s
B3 status section and `svmg_device_arena_code_coresidency_diverges_from_ref_vm_2026-08-07.md`).

## Related

- `doc/08_tracking/lane_matrix.md`
- `src/lib/nogc_sync_mut/test_runner/gpu_lane_common.spl`
- `doc/00_llm_process/feature_expert/gpu_remote_lanes/skill.md`
