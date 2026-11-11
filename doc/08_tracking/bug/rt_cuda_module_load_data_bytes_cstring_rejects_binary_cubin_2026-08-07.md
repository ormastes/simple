# `rt_cuda_module_load_data_bytes` rejects real cubin/fatbin binaries containing embedded NUL bytes
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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

## Triage 2026-09-13 (BUGFIX-7 lane)

Record already states the fix location is entirely inside src/compiler_rust and needs real CUDA hardware to verify -- explicitly architectural-open and out of pure-Simple scope. No change made.


## Fix 2026-11-11 (work/bugfix-cuda-vulkan-20261111)

Fixed the interpreter dlopen twin `rt_cuda_module_load_data_bytes_fn` in
`src/compiler_rust/compiler/src/interpreter_extern/gpu.rs` (interior-NUL-rejecting
`CString::new` replaced with the native twin's `Vec<u8>` copy + terminator pattern,
mirroring `runtime/src/cuda_runtime.rs`). `cargo check -p simple-compiler` PASS.

A/B verified on real NVIDIA GB10 (CC 12.1): a 13,824-byte sm_120 cubin (7,950
interior NULs) loads through the fixed twin (`module_handle > 0`, unload 0); the
same source with the old `CString::new` reproduces this doc's exact
`rt_cuda_module_load_data_bytes does not accept embedded NUL bytes` error.

Pinned spec `x25519mlkem768_cuda_binary_execution_spec.spl` still cannot pass
end-to-end on this host for reasons independent of this fix: read-only seed
lacks the dlopen CUDA layer; tip-tree cross-module visibility rejects the
spec's private fixture import; the interpreter adapter for
`rt_cuda_module_load_data_array` routes to the `not(feature="cuda")` stub
(separate pre-existing gap); the pinned sm_86 cubin is rejected by the CC 12.1
driver (CUDA_ERROR_NO_BINARY_FOR_GPU). Those remain open; the `_bytes` interior
NUL defect itself is closed by this change.
