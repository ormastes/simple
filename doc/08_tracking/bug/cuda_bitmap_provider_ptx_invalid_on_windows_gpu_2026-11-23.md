# CUDA bitmap provider PTX rejected (CUDA_ERROR_INVALID_PTX 218) on Windows GPU

- status: verification-pending
- found: 2026-11-23 while adding nvcuda.dll loading to `src/runtime/providers/cuda/bitmap_provider_v1.c`

With the provider now loading `nvcuda.dll`, a real driver on this Windows host
(1 device) gives `cuInit`, `cuDeviceGetCount`, `cuDeviceGet` and
`cuCtxCreate_v2` all = 0, but `cuModuleLoadData` on the embedded `ptx[]`
(`.version 6.0`, `.target sm_61`) returns 218 (`CUDA_ERROR_INVALID_PTX`), so
`session_open` rejects. Driver loading is not the cause. Next step: get the JIT
log via `cuModuleLoadDataEx` (`CU_JIT_ERROR_LOG_BUFFER`) and fix the PTX text or
target; then extend `src/runtime/test/cuda_driver_load_selfcheck.c` to open a
real session.

## Root cause and fix (2026-11-23, work/ptx1-20261123)

JIT log via `cuModuleLoadDataEx` (CU_JIT_ERROR_LOG_BUFFER) on this host:
`ptxas fatal : SM version specified by .target is higher than default SM version assumed`.
`cuDriverGetVersion` = 9010, device compute capability = 2.1 (Fermi). The
embedded PTX hardcoded `.version 6.0 / .target sm_61`, which the JIT rejects
on any device below sm_61. The kernel only uses sm_20-level instructions, so
`bitmap_provider_v1.c` now queries the device compute capability
(`cuDeviceGetAttribute` 75/76) and prepends the highest supported tier header
(sm_61/6.0, sm_50/4.0, sm_30/3.0, sm_20/3.0) before `cuModuleLoadData`.

Test: `src/runtime/test/cuda_driver_load_selfcheck.c` now JITs the module and
launches `bitmap_and` on 300 elements, checking every output word (exit 77
without a driver). On this Windows box (llvm-mingw clang):
`cuda_driver_load=pass library=nvcuda.dll devices=1 real_context=ok kernel_launch=ok`.
