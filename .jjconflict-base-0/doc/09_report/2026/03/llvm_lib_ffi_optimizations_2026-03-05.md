# LLVM-lib FFI Performance Optimizations Report

**Date:** 2026-03-05
**Status:** Optimizations implemented, pending end-to-end verification

## Summary

Three performance optimizations were implemented for the LLVM-lib backend (LLVM C API via DynLib). These target the hotspots identified in the plan: dlsym lookups, temporary array allocation, and temporary file I/O for object code emission.

## Optimizations Implemented

### P0: FFI Pointer Caching (`src/lib/nogc_sync_mut/ffi/llvm.spl`)

**Problem:** Every LLVM C API call (e.g., `llvm_build_add()`) performed a fresh `spl_dlsym()` lookup via `llvm_lib().callN("LLVMBuildAdd", ...)`. With ~120 LLVM functions and hundreds of calls per compilation, this adds significant overhead.

**Solution:** Added a module-level `_fptr_cache` dictionary that caches `spl_dlsym()` results. Created cached call helpers `_lc0()` through `_lc4()` and `_lcn()` that resolve function pointers once and reuse them on subsequent calls.

**Key code:**
```simple
var _fptr_cache: {text: i64} = {}

fn _llvm_resolve(name: text) -> i64:
    val cached = _fptr_cache[name]
    if cached != nil:
        return cached
    val fptr = spl_dlsym(_llvm_lib.unwrap().handle, name)
    _fptr_cache[name] = fptr
    fptr

fn _lc2(name: text, a0: i64, a1: i64) -> i64:
    spl_wffi_call_i64(_llvm_resolve(name), [a0, a1], 2)
```

**Expected gain:** 10-30% improvement on FFI-heavy code paths (first call has same cost, subsequent calls skip dlsym).

### P0: Memory Buffer Emission (`src/compiler/70.backend/backend/llvm_lib_backend.spl`)

**Problem:** Object code was emitted to a temporary file, then read back into memory, then the temp file was deleted. This added unnecessary disk I/O.

**Solution:** Switched to `llvm_target_machine_emit_to_memory_buffer()` which keeps object code in memory. Added `rt_bytes_from_raw()` runtime function to convert the LLVM memory buffer pointer to a Simple byte array.

**Key code:**
```simple
val mem_buf = llvm_target_machine_emit_to_memory_buffer(tm, llvm_mod, LLVM_OBJECT_FILE)
val buf_ptr = llvm_get_buffer_start(mem_buf)
val buf_size = llvm_get_buffer_size(mem_buf)
val bytes = rt_bytes_from_raw(buf_ptr, buf_size)
llvm_dispose_memory_buffer(mem_buf)
```

**Expected gain:** 5-15% improvement on compilation time (eliminates file write + file read + file delete).

### P1: Scratch Buffer for Small Arrays (`src/lib/nogc_sync_mut/ffi/llvm.spl`)

**Problem:** `llvm_make_array()` was called for every LLVM C API function that takes array arguments (function types, phi nodes, etc.). Each call allocated and freed a new buffer, even for 1-2 element arrays.

**Solution:** Pre-allocated a 64-byte scratch buffer (fits 8 `i64` elements). Arrays of 8 or fewer elements use the scratch buffer instead of calling `rt_alloc()`/`rt_free()`.

**Key code:**
```simple
var _scratch_buf: i64 = 0

fn llvm_make_array(values: [i64]) -> i64:
    val n = values.len()
    if n <= 8:
        val buf = _ensure_scratch()
        for i in 0..n:
            rt_ptr_write_i64(buf, i * 8, values[i])
        return buf
    # Fall through to alloc for larger arrays
    ...

fn llvm_free_array(ptr: i64):
    if ptr != 0 and ptr != _scratch_buf:
        rt_free(ptr)
```

**Expected gain:** 5-10% improvement on FFI calls with array arguments (most LLVM API calls use <= 4 parameters).

## New Runtime Function: `rt_bytes_from_raw`

Added across the full stack:

| File | Change |
|------|--------|
| `src/runtime/runtime_native.c` | C implementation |
| `src/compiler_rust/runtime/src/value/ffi/file_io/file_ops.rs` | Rust implementation |
| `src/compiler_rust/runtime/src/value/ffi/file_io/mod.rs` | Re-export |
| `src/compiler_rust/runtime/src/value/mod.rs` | Re-export |
| `src/compiler_rust/compiler/src/interpreter_extern/file_io.rs` | Interpreter handler |
| `src/compiler_rust/compiler/src/interpreter_extern/mod.rs` | Dispatch entry |
| `src/compiler_rust/compiler/src/codegen/runtime_ffi.rs` | Codegen spec |
| `src/compiler_rust/native_loader/src/static_provider.rs` | Static linking |
| `src/compiler_rust/common/src/runtime_symbols.rs` | Symbol list |

## Verification Status

| Check | Status | Notes |
|-------|--------|-------|
| Rust project builds | PASS | `cargo build --profile bootstrap` succeeds |
| Simple checker passes | PASS | `simple_check llvm.spl` and `llvm_lib_backend.spl` |
| Benchmark harness created | DONE | `test/perf/llvm_lib_ffi_perf_spec.spl` |
| End-to-end llvm-lib compilation | BLOCKED | Stage1 binary has array arg handling bug |
| Rust vs Simple binary comparison | BLOCKED | No working self-hosted binary exists |

## Blockers

1. **Stage1 binary array arg bug:** The natively compiled stage1 binary (`simple native-build`) produces a binary where array element access returns nil in the compile command handler. This prevents testing `compile --native --backend=llvm-lib`.

2. **No self-hosted binary:** `bin/simple` was the Rust bootstrap binary in the referenced period. A working self-hosted binary (compiled by Simple itself) did not currently exist because the stage1 binary was broken.

3. **Interpreter can't handle compile pipeline:** The Rust binary's interpreter cannot resolve the full transitive dependency chain needed for `compile --native --backend=llvm-lib` (fails with `function 'get_effective_backend_name' not found`).

## Next Steps

1. Fix stage1 binary's array element access bug (likely in Cranelift codegen for array indexing)
2. Once stage1 works, compile with `--backend=llvm-lib` to produce stage2
3. Run `test/perf/llvm_lib_ffi_perf_spec.spl` on stage2 to measure actual improvement
4. Compare stage2 (llvm-lib compiled) against Rust binary for lint/fmt/compile workloads
5. Iterate on optimizations until Simple path matches or beats Rust path

## Files Changed

| File | Action | Purpose |
|------|--------|---------|
| `src/lib/nogc_sync_mut/ffi/llvm.spl` | Modified | FFI caching + scratch buffer |
| `src/compiler/70.backend/backend/llvm_lib_backend.spl` | Modified | Memory buffer emission |
| `src/runtime/runtime_native.c` | Modified | `rt_bytes_from_raw` C impl |
| `src/compiler_rust/runtime/src/value/ffi/file_io/file_ops.rs` | Modified | `rt_bytes_from_raw` Rust impl |
| `src/compiler_rust/runtime/src/value/ffi/file_io/mod.rs` | Modified | Re-export |
| `src/compiler_rust/runtime/src/value/mod.rs` | Modified | Re-export |
| `src/compiler_rust/compiler/src/interpreter_extern/file_io.rs` | Modified | Interpreter handler |
| `src/compiler_rust/compiler/src/interpreter_extern/mod.rs` | Modified | Dispatch |
| `src/compiler_rust/compiler/src/codegen/runtime_ffi.rs` | Modified | Codegen spec |
| `src/compiler_rust/native_loader/src/static_provider.rs` | Modified | Static provider |
| `src/compiler_rust/common/src/runtime_symbols.rs` | Modified | Symbol list |
| `test/perf/llvm_lib_ffi_perf_spec.spl` | Created | Benchmark harness |
