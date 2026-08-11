# `rt_cuda_module_load_data_bytes` rejects real cubin/fatbin binaries containing embedded NUL bytes

**Status:** ARCHITECTURAL-OPEN — fix location is entirely inside
`src/compiler_rust/**` (both `runtime/src/cuda_runtime.rs:2402` and
`compiler/src/interpreter_extern/gpu.rs:1540`), which is out of edit scope
for a pure-Simple-only pass; verifying a fix additionally needs a real CUDA
device, which this host lacks (confirmed final terminal-status pass
2026-08-10: `CString::new(bytes)` is still present unchanged at both sites).
**Found:** 2026-08-07
**Component:** `src/compiler_rust/runtime/src/cuda_runtime.rs:2393`
(`rt_cuda_module_load_data_bytes`, `feature = "cuda"` path) and its new
interpreter dlopen-fallback twin in
`src/compiler_rust/compiler/src/interpreter_extern/gpu.rs`
(`rt_cuda_module_load_data_bytes_fn`).
**Attribution:** measured on the Rust bootstrap seed (`bin/simple` prints the
seed banner) after fixing the missing interpreter adapter — see
`doc/08_tracking/bug/rt_cuda_module_load_data_bytes_missing_interpreter_adapter_2026-08-05.md`
(RESOLVED, this is the next layer it uncovered).

## What was found

`test/02_integration/os/crypto/x25519mlkem768_cuda_binary_execution_spec.spl`
now fails past the interpreter-adapter gap with:

```
✗ should load admitted sm86 cubin bytes and execute both NTT entries
  semantic: rt_cuda_module_load_data_bytes does not accept embedded NUL bytes
1 example, 1 failure
```

Both implementations of `rt_cuda_module_load_data_bytes` build a
`CString::new(bytes)` from the raw `(ptr,len)` byte buffer before calling
`cuModuleLoadData`:
- native (`feature = "cuda"`), `cuda_runtime.rs:2393`: `CString::new(bytes)`
  fails silently and returns `-1`.
- interpreter dlopen fallback (this host, no `cuda` cargo feature), just
  added in the sibling fix: same `CString::new(bytes)`, now surfaced as a
  semantic error instead of a silent `-1` (arguably an improvement in
  visibility, but the underlying rejection is the same).

`CString::new` fails on ANY embedded `\0` byte and requires the input not
contain interior NULs. Real cubin/fatbin binaries are compiled machine code
with arbitrary byte content — they routinely contain embedded NUL bytes and
are NOT NUL-terminated C strings. The CUDA Driver API's `cuModuleLoadData`
does not require a NUL-terminated buffer for binary cubin/fatbin images (the
fatbin/cubin container format carries its own length/magic header so the
driver knows where the image ends); the NUL-termination requirement only
applies to legacy plain-text PTX source strings, which is what the sibling
non-`_bytes` function `rt_cuda_module_load_data` is for.

So `rt_cuda_module_load_data_bytes` — the function specifically added to take
an explicit `(ptr,len)` pair so length-tracked *binary* buffers wouldn't need
to be NUL-safe — reintroduces exactly the NUL-termination constraint it was
meant to avoid, by routing through `CString` instead of passing the raw
pointer+length straight to the driver call.

## Suspected fix (not yet implemented — separate task)

Call `cuModuleLoadData(&mut module, ptx_ptr as *const c_void)` directly with
the raw pointer (no `CString` round-trip), since cubin/fatbin images are
self-describing. If the underlying buffer is not guaranteed NUL-terminated
and the driver ever needs an explicit end marker for defensive reasons, use
`cuModuleLoadFatBinary` or ensure the caller (`.spl` cubin-loading path)
appends a defensive NUL terminator *after* materializing the array via
`rt_array_data_ptr_u8`, rather than rejecting valid binaries here. Needs a
real CUDA host to verify `cuModuleLoadData` behavior on binary input; this
host has no CUDA device, only a discoverable `libcuda.so` via dlopen, so the
call reaches real driver marshaling but can't be confirmed against actual
GPU execution.

## Reproduce

```
SIMPLE_TIMEOUT_SECONDS=0 SIMPLE_RUST_SEED_WARNING=0 bin/simple test \
  test/02_integration/os/crypto/x25519mlkem768_cuda_binary_execution_spec.spl \
  --no-cache --no-cover-check
```
