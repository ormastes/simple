# `rt_cuda_module_load_data_bytes` has no interpreter adapter — next layer after `rt_array_data_ptr_u8`

**Status:** OPEN
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
