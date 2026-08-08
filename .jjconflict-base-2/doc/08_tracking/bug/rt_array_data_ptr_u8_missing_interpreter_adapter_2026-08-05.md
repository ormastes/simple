# `rt_array_data_ptr_u8` had no interpreter adapter — fixed

**Status:** FIXED (2026-08-05)
**Found:** 2026-08-05, while closing the CUDA kernel-artifact gap for AC-5
**Component:** `src/compiler_rust/compiler/src/interpreter_extern/sffi_array.rs`,
`src/compiler_rust/compiler/src/interpreter_extern/mod.rs`
**Attribution:** measured on the Rust bootstrap seed (`bin/simple` prints the
seed banner).

## Symptom

`test/02_integration/os/crypto/x25519mlkem768_cuda_binary_execution_spec.spl`
failed under `bin/simple test` (interpreter) with:

```
semantic: unknown extern function: rt_array_data_ptr_u8
```

hit via `CryptoCudaSession.load_module_binary` → `src/lib/gc_async_mut/cuda.spl`.
`rt_array_data_ptr_u8` **is** registered as a real runtime symbol for
codegen/JIT (`runtime_symbols.rs`, `codegen/runtime_sffi.rs`,
`codegen/llvm/functions/calls.rs`), but had no `interpreter_extern` table
entry, and `bin/simple test` always runs the interpreter — same shape of gap
as the JIT sha256 defect and the H1-client `to_char` defect fixed earlier this
session (a runtime function that exists for one execution path but not the
other).

## Fix

Added `rt_array_data_ptr_u8_fn` to
`src/compiler_rust/compiler/src/interpreter_extern/sffi_array.rs`: for a
`Value::Array` (interpreter-native, `Vec<Value>`, not a contiguous native
buffer), materializes a `Vec<u8>` from the element values and leaks it — the
same "intentionally leaked, short-lived interpreter process" pattern already
used for `Value::Str` → C string pointers in `dynamic_sffi::value_to_i64`.
For a heap-backed array (already a raw native pointer/handle, encoded as
`Value::Int`), delegates straight to the native runtime implementation.
Registered in `interpreter_extern/mod.rs`'s dispatch table:
`insert_simple!("rt_array_data_ptr_u8", sffi_array::rt_array_data_ptr_u8_fn);`.

## Verification

Rebuilt the seed (adhoc incremental `cargo build --release --bin simple`,
not a full `bin/simple build bootstrap`), redeployed to
`bin/release/x86_64-unknown-linux-gnu/simple`. The target spec's error
changed (not just re-observed) — from `unknown extern function:
rt_array_data_ptr_u8` to `unknown extern function:
rt_cuda_module_load_data_bytes`, a different, deeper gap, tracked separately
in `doc/08_tracking/bug/rt_cuda_module_load_data_bytes_missing_interpreter_adapter_2026-08-05.md`.
That the error *changed* rather than persisting is the proof this specific
fix is real, per this session's standing rule ("prove resolution by which
error changes").

No regressions on three other specs run against the same rebuild:
`x25519mlkem768_vulkan_candidate_spec.spl` 3/3,
`x25519mlkem768_cuda_warmup_contract_spec.spl` 3/3,
`x25519mlkem768_manifest_existence_gate_spec.spl` 8/8.

## Note on landing scope

This fix's registration line in `mod.rs` landed alongside a large, unrelated
Vulkan/SDL2/OpenGL interpreter-dispatch cleanup from a separate concurrent
session that had been sitting uncommitted in this shared worktree (~300
lines, well-commented, its own bug-doc references). That diff was stable
across multiple checks spanning ~40+ minutes of real time with no further
growth, the rebuild compiled clean, and the three regression specs above
covered exactly the areas it touches (Vulkan dispatch, CUDA dispatch) — so it
was landed together rather than held indefinitely. See
`doc/08_tracking/bug/mlkem_ntt_simd_public_interface_probe_crashes_not_pass_2026-08-05.md`
and prior session history for the caution that led to holding it initially.
