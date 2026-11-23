# C CUDA provider only opens libcuda.so.1 (no Windows CUDA)

- status: open
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
