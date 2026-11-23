# CUDA bitmap provider PTX rejected (CUDA_ERROR_INVALID_PTX 218) on Windows GPU

- status: open
- found: 2026-11-23 while adding nvcuda.dll loading to `src/runtime/providers/cuda/bitmap_provider_v1.c`

With the provider now loading `nvcuda.dll`, a real driver on this Windows host
(1 device) gives `cuInit`, `cuDeviceGetCount`, `cuDeviceGet` and
`cuCtxCreate_v2` all = 0, but `cuModuleLoadData` on the embedded `ptx[]`
(`.version 6.0`, `.target sm_61`) returns 218 (`CUDA_ERROR_INVALID_PTX`), so
`session_open` rejects. Driver loading is not the cause. Next step: get the JIT
log via `cuModuleLoadDataEx` (`CU_JIT_ERROR_LOG_BUFFER`) and fix the PTX text or
target; then extend `src/runtime/test/cuda_driver_load_selfcheck.c` to open a
real session.
