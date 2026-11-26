# rt_cuda_module_get_function takes a C string for a Simple `text` argument

**Status:** OPEN. **Found:** 2026-11-26 (work/bug-cuda-native-20261126). **Severity:** P3.
**Component:** `src/compiler_rust/runtime/src/cuda_runtime.rs`, `src/runtime/runtime_dynload.c`.

The Rust `rt_cuda_module_get_function(module: i64, func_name: *const c_char)`
reads its name as a NUL-terminated C string. The Simple extern declares
`func_name: text`, whose native ABI is `(bytes, byte length)`, as for
`rt_cuda_launch_kernel` and `rt_cuda_launch_kernel_ex`. The core-C forwarder
set in `runtime_dynload.c` therefore leaves this one function out (27 of 28
forwarded) until the ABI is decided.

Found while fixing `native_c_runtime_missing_cuda_provider_forwarders_2026-11-22`.
