# BUG: CUDA lane init fails with `cuda-lane-device-identity-unavailable` on a host with healthy GPUs

**Status:** RESOLVED 2026-08-08, commit `5c49e3538f9cfbd05f5bdcb45ad2d386586a0244`
**File:** `src/lib/gc_async_mut/gpu_lane/cuda_lane_session.spl` (`probe()` / `init()` device-identity path)
**Date filed:** 2026-08-08 (rewritten same day — original root cause was wrong)
**Severity:** HIGH — blocks all CUDA lane device verification (B1/B2/B3)

## Root cause (confirmed 2026-08-08)

Not a `.spl` defect and not a driver-level error. `rt_cuda_device_name_fn`'s
`#[cfg(not(feature = "cuda"))]` branch in
`src/compiler_rust/compiler/src/interpreter_extern/gpu.rs` — the dlopen
fallback used by the tree-walk interpreter path (`bin/simple test` on this
host, which is not built with the `cuda` Cargo feature) — was a hardcoded
`Ok(Value::text(String::new()))` stub. It never called `cuDeviceGetName`, and
the dlopen `CudaFns` struct never even loaded that symbol, unlike its
siblings (`device_get`, `device_get_uuid`, `ctx_create`, `ctx_synchronize`),
which correctly `dlsym` + dispatch to the real driver. Every other probe/init
step (`cuda_available`, `cuda_init`, `cuda_device_count`, `cuda_device_get`,
`cuda_ctx_create`, `cuda_device_identity` via `cuDeviceGetUuid`) reaches the
real driver and can succeed; `stable_device_name()` could not, on any host,
healthy or not — so `CudaLaneSession.init()`'s `device_name == "" or
device_identity <= 0` check tripped unconditionally via the name half of the
OR. This is why the standalone C harness (calling the driver directly)
succeeded while the Simple binding failed: the defect never reached the
driver for this one call.

**Fix:** added the missing `CuDeviceGetName` symbol load to the dlopen
`CudaFns` struct and wired `rt_cuda_device_name_fn`'s fallback branch through
it, mirroring the existing `device_get_uuid` pattern.

**Verified:** `test/02_integration/gpu_lane/cuda_lane_session_spec.spl` 3/4 ->
4/4. Sabotage-probed (reverted -> 3/4 RED, restored -> 4/4 GREEN, rebuilt and
redeployed the seed at each step).
`test/03_system/gpu_lane/cuda_vm_executor_conformance_spec.spl` improved 0/2
-> 1/2 (device identity now resolves; the remaining failure is a distinct,
downstream defect inside the D3 conformance vector runner itself — see
`doc/08_tracking/bug/cuda_vm_executor_conformance_array_index_out_of_bounds_2026-08-08.md`).
`test/03_system/gpu_lane/cuda_jit_hello_spec.spl` unchanged at 13/14 (its RED
is the separate, already-filed `cuda-jit-backend-compile-failed` /
`rt_cuda_module_load_data_bytes` NUL-rejection defect, not this one).

## Summary

`CudaLaneSession.probe()` returns `""` (meaning "device usable, proceed"), and the
subsequent `init()` then fails with `cuda-lane-device-identity-unavailable`.

The original version of this bug doc claimed the cause was "running on a host
without CUDA device support", and treated the probe's failure to predict that as
the defect. **That premise was false and is retracted.** The host is healthy; the
Simple CUDA path is not.

## Evidence that the device is genuinely healthy

Measured on the failing host, 2026-08-08:

- Two working NVIDIA GPUs: `NVIDIA RTX A6000`, `NVIDIA TITAN RTX` (via `nvidia-smi`).
- Kernel module `NVRM version: ... 580.126.16` (`/proc/driver/nvidia/version`).
- `/usr/lib/x86_64-linux-gnu/libcuda.so.1 -> libcuda.so.580.126.16` — userspace
  matches the kernel module exactly. **No driver/userspace version skew.**
  (A stale `libcuda.so.535.247.01` is present on disk but is NOT the one linked;
  it was checked and ruled out as a cause.)
- `nvidia-smi` queries succeed.

So device identity is failing where the driver stack is fully functional. This is
a defect in the Simple CUDA lane, not an environment limitation.

## Impact

`test/03_system/gpu_lane/cuda_vm_executor_conformance_spec.spl` cannot run any
D3 conformance vector on the device. It is therefore **legitimately RED** on this
host, per `.claude/rules/testing.md` ("a correct spec that fails is a legitimate
artifact").

Note: an earlier revision of that spec papered over this with a literal
`assert_true(true)`, producing a vacuous "2 passed" while executing zero
conformance vectors. That false green has been removed; the spec now fails
honestly and will go green once this bug is fixed.

## Related / possibly same root cause

These are all CUDA-path failures observed on the same healthy host and should be
triaged together — they may share one underlying cause:

- `doc/08_tracking/bug/cuda_lane_session_create_unresolved_across_module_boundary_2026-08-07.md`
  — session create extern unresolved across a module boundary.
- `doc/08_tracking/bug/rt_cuda_module_load_data_bytes_cstring_rejects_binary_cubin_2026-08-07.md`
- `test/02_integration/gpu_lane/cuda_lane_session_spec.spl` — 3/4, its one RED is
  this same `cuda-lane-device-identity-unavailable`.
- `test/03_system/gpu_lane/cuda_jit_hello_spec.spl` — 13/14, RED is
  `cuda-jit-backend-compile-failed` on the same host.

By contrast the Vulkan lane on this same host works: `vulkan_jit_hello_spec` is
2/2 and `vulkan_vm_executor_conformance_spec` is 2/2 — so the failure is specific
to the CUDA path, not to GPU access in general.

## Unblock condition

Determine why device identity lookup fails after device get / context create
succeed, on a host where `libcuda` and the kernel module match. Concretely:

1. Instrument the CUDA driver-API call sequence in `cuda_lane_session.spl` and
   capture the actual `CUresult` code at the first failing call (do not infer it
   from the wrapped error string).
2. Confirm whether the failure is in the extern binding/marshalling layer (see
   the module-boundary bug above) rather than in the driver call itself — a
   standalone C harness against the same driver API succeeded during B3, which
   points at the Simple binding layer, not CUDA.
3. Fix, then this spec and the RED examples in the two specs above should all go
   green with no assertion changes.

Do NOT close this by weakening any assertion.
