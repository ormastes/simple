# rt_cuda_launch_kernel_ex: native callers pass a C string, Rust reads (ptr, len)

**Status:** OPEN. **Found:** 2026-11-26 (work/bug-cuda-module-get-function-abi-20261126). **Severity:** P2.
**Component:** `src/compiler/50.mir/text_extern_abi.spl`, `src/compiler_rust/runtime/src/cuda_runtime.rs`.

Native codegen splits a `text` extern argument into `(bytes, len)` only for
names that have a row in `text_arg_indices` (`text_extern_abi.spl`). Every
other text argument is passed as ONE word, the `rt_interp_cstr` C-string
pointer. Disassembly of a native probe shows exactly this:
`rt_cuda_module_get_function(module, "name")` gets `x1 = rt_interp_cstr(...)`
and nothing in `x2`.

`rt_cuda_launch_kernel_ex` has no row, but its Rust definition takes
`(module, func_name_ptr: *const u8, func_name_len: u64, ...)`. A native
caller therefore shifts every later argument by one slot, and `func_name_len`
becomes the caller's `grid_x`. Native callers exist:
`src/lib/nogc_sync_mut/cuda/mod.spl:121`,
`src/lib/nogc_sync_mut/io/cuda_sffi.spl:268`,
`src/lib/nogc_async_mut/cuda/mod.spl:857`.

Not fixed here. The fix is either a `text_extern_abi.spl` row (which works
only in a compiler rebuilt from that source, so it must land in lockstep with
a bootstrap) or a C-string Rust signature. That choice belongs to the owner.
`rt_cuda_launch_kernel`, which has a row, is consistent.
