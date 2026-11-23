# C CUDA provider only opens libcuda.so.1 (no Windows CUDA)

- status: verification-pending
- found: 2026-11-23 while wiring `cuda_driver()` into `std.gc_async_mut.cuda` entry points
- design: doc/05_design/lib/runtime/cuda_driver_dynamic_load.md

The Simple-side gate (`cuda_driver()`) resolves `nvcuda.dll` on Windows, but the
`rt_cuda_*` calls behind it still go through the C provider, which dlopens only
`libcuda.so.1`. On Windows the gate passes and the provider then reports no CUDA.
The Rust seed loader is a separate path with its own candidate list.

Fix (owner of the C provider / seed): either back `rt_cuda_*` with the symbols
already resolved by `cuda_driver()`, or teach the provider the same candidate
list (`nvcuda.dll`; `libcuda.so.1`, `libcuda.so`). Not changed in the wiring PR
by instruction.

## Fix (2026-11-23, work/cud3-20261123)

`src/runtime/providers/cuda/bitmap_provider_v1.c` now loads `nvcuda.dll`
(LoadLibraryA/GetProcAddress) on Windows and `libcuda.so.1`, `libcuda.so`
elsewhere; symbols resolve into one table published once by atomic CAS; load
failures are the named `CUDA-E001` / `CUDA-E002` errors
(`simple_cuda_provider_last_error_v1`). Test:
`src/runtime/test/cuda_driver_load_selfcheck.c` — real `cuInit`, device count 1
and a real context on this Windows GPU host (llvm-mingw clang); E001/E002 cases
also pass on Linux. Follow-up: the provider's embedded PTX is rejected by this
driver, see `cuda_bitmap_provider_ptx_invalid_on_windows_gpu_2026-11-23.md`.
