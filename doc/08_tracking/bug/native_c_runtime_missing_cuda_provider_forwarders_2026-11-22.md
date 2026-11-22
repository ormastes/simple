# Native C runtime has no forwarders for 28 CUDA externs; native programs using std device queries fail to link (2026-11-22)

**Status:** OPEN. **Found:** 2026-11-22 (work/cuda-runtime-bugs). **Component:** `src/runtime/runtime_dynload.c` (GPU provider dispatch).

## Symptom
integ25 Stage 2 (sha256 `ef46f0d2ab4274c4`), `native-build --backend=llvm --entry-closure` of
`use std.gc_async_mut.gpu_ops.*` + `gpu_init()` / `gpu_device_count()` /
`gpu_device_compute_capability(0)`:

```
ld.lld: error: undefined symbol: rt_cuda_device_compute_capability
ld.lld: error: undefined symbol: rt_cuda_device_get
ld.lld: error: undefined symbol: rt_cuda_get_error_string
```

## Cause
`simple_cuda_required[]` (runtime_dynload.c:199) requires the provider DSO to export these
symbols, but only a subset has a `GPU_CALLn` forwarder in the base executable
(runtime_dynload.c:1688-1712). Static diff of the `extern fn rt_cuda_*` set in
`src/lib/nogc_sync_mut/cuda/sffi.spl` against the forwarders: 28 externs have no definition in
the C runtime:

rt_cuda_ctx_create rt_cuda_ctx_destroy rt_cuda_ctx_set_current rt_cuda_ctx_synchronize rt_cuda_device_compute_capability rt_cuda_device_get rt_cuda_device_identity rt_cuda_device_name rt_cuda_f64_binary_op rt_cuda_f64_minmax rt_cuda_f64_scalar_div rt_cuda_f64_slice_1d rt_cuda_f64_slice_2d rt_cuda_f64_sum rt_cuda_f64_sum_axis rt_cuda_get_error_string rt_cuda_launch_kernel rt_cuda_launch_kernel_name rt_cuda_memcpy_dtod rt_cuda_memcpy_htod rt_cuda_mem_free rt_cuda_memset rt_cuda_module_get_function rt_cuda_module_load rt_cuda_module_load_data rt_cuda_module_load_data_bytes rt_cuda_module_unload rt_cuda_sync 

Of these, 16 are already in `simple_cuda_required[]` (the provider must export them), so a
forwarder is a mechanical `GPU_CALLn` row each; the other 12 (`f64_*`, `module_load`,
`module_get_function`, `launch_kernel`, `device_identity`, `module_load_data`) need an
ABI decision first.

## Acceptance
Native-build the fixture above with a provider (`build/sffi/libsimple_gpu_cuda.so` via
`scripts/build/build_simple_runtime_sffi.shs`, `SIMPLE_CUDA_PROVIDER_PATH` +
`SIMPLE_CUDA_PROVIDER_SHA256`) and see the live count and capability; without a provider it must link and report 0 devices.
Extend `scripts/check/check-gpu-provider-dynload-registry.shs` to cover the new forwarders.

## Also seen on the same Stage 2 (not chased)
- `use std.cuda.*` (→ `nogc_async_mut/cuda/mod.spl`) fails HIR: `unresolved name: id` at
  `mod.spl:688:17` and `Device.CUDA pattern has 1 slot(s), declaration has 0`.
- cranelift: `Failed to compile function: lib.gc_async_mut.gpu_ops.gpu_load_f32`.
