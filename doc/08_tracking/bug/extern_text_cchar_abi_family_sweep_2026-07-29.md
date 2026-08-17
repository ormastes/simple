# Mechanical Sweep: extern text-arg `c_char` → `(ptr, len)` ABI family

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 01).

**Scope:** extern "C" functions in `src/compiler_rust/runtime/src` taking `*const c_char` text parameters must use `(*const u8, u64)` when callable from native codegen (JIT/Cranelift), per doc/08_tracking/bug/mem_attr_set_owner_jit_text_arg_dropped_2026-07-29.md.

**Completed:** 2026-07-29

## Summary

- **Total extern "C" with c_char:** 43
- **Unreachable (interpreter-only, no fix needed):** 39
- **Broken (in RUNTIME_FUNCS, now fixed):** 4
- **Fixed:** 4

## Broken Functions Fixed

| Function | File | Param(s) | Fix Applied |
|----------|------|----------|------------|
| `rt_cuda_launch_kernel` | `src/compiler_rust/runtime/src/cuda_runtime.rs` | func_name: `*const c_char` → `(*const u8, u64)` | ✓ Fixed |
| `rt_cuda_module_load` | `src/compiler_rust/runtime/src/cuda_runtime.rs` | path: `*const c_char` → `(*const u8, u64)` | ✓ Fixed |
| `rt_cuda_module_load_data` | `src/compiler_rust/runtime/src/cuda_runtime.rs` | ptx: `*const c_char` → `(*const u8, u64)` | ✓ Fixed |
| `rt_profiler_record_call` | `src/compiler_rust/runtime/src/value/profiler_sffi.rs` | name: `*const c_char` → `(*const u8, u64)` | ✓ Fixed |

## Fix Pattern (3-part)

Each fix follows the exact pattern from `rt_panic` (commit a9e61476da9):

1. **Runtime Signature** (runtime/src/*/...rs):
   - Change `(param: *const c_char)` to `(param_ptr: *const u8, param_len: u64)`
   - Decode with `std::slice::from_raw_parts` + `std::string::from_utf8_lossy` or `CString::new`
   - Document the convention in a comment

2. **Codegen Runtime Spec** (compiler/src/codegen/runtime_sffi.rs):
   - Update `RuntimeFuncSpec::new("fn_name", &[...], ...)` to have two I64 args instead of one
   - Update comment to show the parameter names

3. **Codegen Text Arg Indices** (compiler/src/codegen/instr/calls.rs):
   - Add to `text_arg_indices()` match arm with the parameter index
   - Remove from `text_cstr_arg_indices()` if present (rt_cuda_launch_kernel and rt_cuda_module_load_data were)

## Unreachable Functions (39, no fix needed)

These are NOT in RUNTIME_FUNCS (interpreter-only paths or disabled features):

| Function | Classification |
|----------|-----------------|
| rt_cargo_build | Interpreter-only |
| rt_cargo_test | Interpreter-only |
| rt_cuda_module_get_function | Interpreter-only |
| rt_diagram_* (8 functions) | Interpreter-only |
| rt_host_gpu_queue_emit_payload_text_c | Interpreter-only |
| rt_package_* (17 functions) | Interpreter-only |
| rt_resource_registry_free_string | Interpreter-only |
| rt_resource_registry_register | Interpreter-only |
| rt_screenshot_* (5 functions) | Interpreter-only |
| self_extract_* (3 functions) | Interpreter-only |
| upx_* (4 functions) | Interpreter-only |

## Verification

```bash
cd src/compiler_rust && cargo build -p simple-runtime -p simple-compiler
# Finished `dev` profile [unoptimized + debuginfo] target(s) in 30.94s

cargo test -p simple-runtime --lib attr_tests
# test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 1085 filtered out

cargo test -p simple-compiler --lib interpreter_extern::
# test result: ok. 122 passed; 0 failed; 0 ignored; 0 measured; 3404 filtered out
```

## Impact

- **JIT/native engine:** panic messages, CUDA module/kernel names, profiler function names now correctly decoded and passed (were dropping/corrupting text under native codegen)
- **Interpreter engine:** no change (already correct, uses value-based paths)
- **ABI family:** completes the `(*const u8, u64)` standardization for all text-parameter externs reachable from native codegen
