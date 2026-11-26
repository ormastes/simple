# rt_cuda_module_load_data rejects valid PTX; a failed module handle SEGVs in libcuda

**Status:** VERIFIED 2026-11-26 (GB10, aarch64). **Found:** 2026-11-26 (work/bug-cuda-module-get-function-abi-20261126). **Severity:** P2.
**Component:** `src/compiler_rust/runtime/src/cuda_runtime.rs`.

## Symptoms
1. `rt_cuda_module_load_data(ptx: text)` returned -218 (`CUDA_ERROR_INVALID_PTX`)
   for PTX that loads fine as a C string. The `(ptr, len)` span is not
   NUL-terminated, but the code handed `bytes.as_ptr()` straight to
   `cuModuleLoadData`, which parses PTX as a C string and reads past `len`.
2. Passing that failed (negative) module handle on to
   `rt_cuda_module_get_function` or `rt_cuda_launch_kernel` crashed the
   process: SIGSEGV inside `libcuda.so.1` (`cuModuleGetFunction`).

## Reproduction (dlopen harness against the provider `libsimple_runtime.so`)
- Same PTX, with and without a terminator after `len`: before the fix
  `nul_term=<handle> no_nul=-218`; after it, both return a handle.
- `rt_cuda_module_get_function(-218, "probe_fill")`: before the fix, rc 139
  (SIGSEGV); after it, -1. `rt_cuda_launch_kernel(-218, ...)`: -1.

## Resolution
- `rt_cuda_module_load_data` copies the span and appends a NUL, as
  `rt_cuda_module_load_data_bytes` already did.
- `rt_cuda_module_get_function`, `rt_cuda_launch_kernel` and
  `rt_cuda_launch_kernel_ex` return -1 (`CUDA_ERROR_INVALID_VALUE`) for a
  module handle <= 0 instead of passing it to the driver.
- End to end: `src/app/test/cuda_module_launch_probe.spl`, built natively,
  loads its PTX, resolves `probe_fill`, launches it and reads 4/4 sentinels
  back on the GB10.
