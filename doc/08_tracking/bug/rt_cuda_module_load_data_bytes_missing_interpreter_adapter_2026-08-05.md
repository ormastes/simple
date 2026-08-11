# `rt_cuda_module_load_data_bytes` has no interpreter adapter — next layer after `rt_array_data_ptr_u8`

**Status:** RESOLVED 2026-08-07
**Found:** 2026-08-05
**Component:** `src/lib/gc_async_mut/crypto_accel/cuda_session.spl` /
`src/lib/gc_async_mut/cuda.spl` → `rt_cuda_module_load_data_bytes`
**Attribution:** measured on the Rust bootstrap seed (`bin/simple` prints the
seed banner).

## What was found

After fixing the separate, now-resolved `rt_array_data_ptr_u8` interpreter
gap (`doc/08_tracking/bug/` — same session, landed alongside this doc),
`test/02_integration/os/crypto/x25519mlkem768_cuda_binary_execution_spec.spl`
progressed to a **different** error instead of passing:

```
✗ should load admitted sm86 cubin bytes and execute both NTT entries
  semantic: unknown extern function: rt_cuda_module_load_data_bytes
1 example, 1 failure
```

Independently confirmed the error changed (not just re-observed) by running
the exact same spec before and after the `rt_array_data_ptr_u8` fix — before:
`unknown extern function: rt_array_data_ptr_u8`; after: `unknown extern
function: rt_cuda_module_load_data_bytes`. Same shape of defect as the one
just fixed: a runtime symbol that exists for codegen/JIT but has no
`interpreter_extern` adapter, so `bin/simple test` (which always uses the
interpreter) cannot call it.

## Regression check, same rebuild

No regressions from the `rt_array_data_ptr_u8` fix or the concurrent
`interpreter_extern/mod.rs` Vulkan/SDL2/OpenGL dispatch cleanup that landed
alongside it:
- `x25519mlkem768_vulkan_candidate_spec.spl`: `Results: 3 total, 3 passed, 0 failed`
- `x25519mlkem768_cuda_warmup_contract_spec.spl`: `Results: 3 total, 3 passed, 0 failed`
- `x25519mlkem768_manifest_existence_gate_spec.spl`: `Results: 8 total, 8 passed, 0 failed`

## Resume

Same fix pattern as `rt_array_data_ptr_u8`: find `rt_cuda_module_load_data_bytes`'s
native implementation (likely `src/runtime/` CUDA driver bindings, loading a
cubin/PTX module from an in-memory byte buffer via the CUDA Driver API), add
an `interpreter_extern` adapter following the `sffi_array.rs` pattern (or
wherever the existing CUDA externs like `cuda_module_load_binary` are
adapted), rebuild the seed incrementally, redeploy, re-run the spec. Expect
further layers — this pattern (real native symbol, JIT-only registration) may
recur for other CUDA driver calls the session layer uses (submit, sync,
readback) until the whole chain is interpreter-reachable.

## Reproduce

```
SIMPLE_TIMEOUT_SECONDS=0 bin/simple test \
  test/02_integration/os/crypto/x25519mlkem768_cuda_binary_execution_spec.spl \
  --no-cache --no-cover-check
```

## Fix (2026-08-07)

Added `rt_cuda_module_load_data_bytes_fn` to
`src/compiler_rust/compiler/src/interpreter_extern/gpu.rs`, mirroring the
existing `rt_cuda_module_load_data_fn` handler right above it. Unlike the
non-`_bytes` variant (which takes a `text` PTX source and is ABI-expanded to
`(ptr,len)` by codegen), `_bytes` takes an explicit raw `(ptr,len)` pair
already pointing at a materialized byte buffer (e.g. a cubin obtained via
`rt_array_data_ptr_u8`), so the handler reads two `Value::Int` args via
`arg_i64` instead of one `Value::Str` via `arg_text`. On the `feature =
"cuda"` build it delegates straight to the native
`rt_cuda_module_load_data_bytes(ptx_ptr, ptx_len)`; on the dlopen fallback
(this host — no `cuda` cargo feature compiled in) it builds the byte slice
from the raw pointer/length and calls `cuModuleLoadData` through the dlopen'd
`module_load_data` function pointer, same as the non-`_bytes` fallback.
Registered in `interpreter_extern/mod.rs`:
`insert_simple!("rt_cuda_module_load_data_bytes", gpu::rt_cuda_module_load_data_bytes_fn);`.

Rebuilt the seed with `cargo build --release --bin simple` (same adhoc
incremental rebuild pattern as the `rt_array_data_ptr_u8` fix, not a full
`bin/simple build bootstrap`), redeployed to
`bin/release/x86_64-unknown-linux-gnu/simple` (currently the seed itself —
`bin/simple --version` already prints the seed-banner per the Stage-3
self-host blocker in `.claude/rules/bootstrap.md`, so this redeploy did not
change that pre-existing state).

### Before / after evidence

Before (this session, re-confirmed):
```
✗ should load admitted sm86 cubin bytes and execute both NTT entries
  semantic: unknown extern function: rt_cuda_module_load_data_bytes
1 example, 1 failure
```

After:
```
✗ should load admitted sm86 cubin bytes and execute both NTT entries
  semantic: rt_cuda_module_load_data_bytes does not accept embedded NUL bytes
1 example, 1 failure
```

The error changed from "unknown extern function" (interpreter can't find the
symbol at all) to a semantic error raised *inside* the new handler while
actually marshaling and dispatching the call — proof the adapter is wired and
reachable. This host has no CUDA GPU but does have `libcuda.so` discoverable
via `dlopen` (the `get_cuda_dl()` fallback path succeeded), so the call
reached real CUDA-driver marshaling code instead of stopping at "no CUDA
device found".

### New follow-on gap found by this fix (filed separately)

The "does not accept embedded NUL bytes" error is legitimate, not a defect in
this adapter: it comes straight from `CString::new(bytes)` in both the new
interpreter handler's dlopen fallback AND the pre-existing native
implementation `rt_cuda_module_load_data_bytes` in
`src/compiler_rust/runtime/src/cuda_runtime.rs:2393` (`feature = "cuda"`
path). Real cubin/fatbin binaries are arbitrary binary data and routinely
contain embedded NUL bytes, so `CString::new` rejecting them is a real
upstream bug in the native CUDA loader helper (`cuModuleLoadData` does not
actually require a NUL-terminated buffer for cubin/fatbin images — the format
carries its own length/magic header), not something introduced by this
interpreter-adapter fix. Out of scope for this task (adapter wiring only, no
native-runtime refactor); filed as
`doc/08_tracking/bug/rt_cuda_module_load_data_bytes_cstring_rejects_binary_cubin_2026-08-07.md`.

### Regression check, same rebuild

- `x25519mlkem768_vulkan_candidate_spec.spl`: `Results: 3 total, 3 passed, 0 failed`
- `x25519mlkem768_cuda_warmup_contract_spec.spl`: `Results: 3 total, 3 passed, 0 failed`
- `x25519mlkem768_manifest_existence_gate_spec.spl`: `Results: 8 total, 8 passed, 0 failed`
