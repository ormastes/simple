# CUDA Direct FFI Phase 4 - Blocked by Generator Bugs

**Date:** 2026-02-09
**Status:** ⚠️ BLOCKED
**Session:** CUDA Unified Interface Implementation

---

## Summary

Attempted to implement Phase 4 (Direct CUDA FFI) using the SFFI wrapper generator tool. Discovered critical bugs in the wrapper generator that prevent correct code generation for CUDA bindings. Phase 4 is blocked pending generator fixes.

---

## What Was Attempted

### Goal
Create native CUDA C API bindings without PyTorch dependency using the three-tier SFFI pattern:
- **Tier 1:** C++ bridge (`.build/rust/ffi_cuda/`)
- **Tier 2:** Simple FFI bindings (`src/lib/cuda/ffi.spl`)
- **Tier 3:** Simple API (`src/lib/cuda/mod.spl`)

### Approach
1. Created `examples/cuda.wrapper_spec` with CUDA handle types and functions
2. Used single-line lambda syntax for `cpp_fn` and `cpp_method`
3. Ran `bin/simple wrapper-gen examples/cuda.wrapper_spec`
4. Expected: Clean 3-tier CUDA FFI bindings
5. Actual: Generated code with syntax errors

---

## Generator Bugs Discovered

### Bug #1: Lambda Argument Mismatch for Handle Parameters

**Location:** `.build/rust/ffi_cuda/src/bridge.cpp:116, 124, 159`

**Problem:** When a `cpp_fn` lambda has handle-type parameters, the generator passes `.inner` to the lambda call instead of the full handle.

**Generated Code (WRONG):**
```cpp
bool cuda_memcpy_d2d(const CudaDeviceMem& dst, const CudaDeviceMem& src, int64_t size_bytes) {
#ifdef HAS_CUDA
    return [](const CudaDeviceMem& dst, const CudaDeviceMem& src, i64 size_bytes) {
        return cudaMemcpy(dst.inner, src.inner, size_bytes, cudaMemcpyDeviceToDevice) == cudaSuccess;
    }(dst.inner, src.inner, size_bytes);  // ❌ WRONG: passes .inner to lambda expecting full handle
#else
    return false;
#endif
}
```

**Should Be:**
```cpp
}(dst, src, size_bytes);  // ✅ Pass full handles, lambda extracts .inner
```

**Root Cause:** Generator assumes lambda parameters are primitive types and tries to "unwrap" handle types by passing `.inner`.

---

### Bug #2: Invalid Method Lambda Syntax

**Location:** `.build/rust/ffi_cuda/src/bridge.cpp:191, 199, 207, etc.`

**Problem:** When a `cpp_method` contains a lambda, the generator produces invalid `h.inner.lambda()` syntax.

**Generated Code (WRONG):**
```cpp
bool cuda_cudastream_synchronize(const CudaStream& h) {
#ifdef HAS_CUDA
    return h.inner.[](const CudaStream& h) {
        return cudaStreamSynchronize(h.inner) == cudaSuccess;
    }();  // ❌ WRONG: h.inner is not an object, can't call lambda on it
#else
    return false;
#endif
}
```

**Should Be:**
```cpp
bool cuda_cudastream_synchronize(const CudaStream& h) {
#ifdef HAS_CUDA
    return cudaStreamSynchronize(h.inner) == cudaSuccess;
#else
    return false;
#endif
}
```

**Root Cause:** Generator treats `cpp_method` lambdas as member functions of `h.inner` instead of standalone lambdas or inline code.

---

### Bug #3: Wrong Function Names in Tier 3

**Location:** `src/lib/cuda/mod.spl:34, 38, 73, 108`

**Problem:** Generated Tier 3 calls have wrong FFI function names.

**Generated Code (WRONG):**
```simple
static fn cuda_stream_create() -> CudaStreamWrapper:
    val handle = rt_cuda_cuda_stream_create()  # ❌ Double "cuda_"
    CudaStreamWrapper(handle: handle, owns_handle: true)
```

**Should Be:**
```simple
val handle = rt_cuda_stream_create()  # ✅ Correct FFI name
```

**Root Cause:** Generator prefixes function name with library name twice (`rt_cuda_` + `cuda_stream_create` → `rt_cuda_cuda_stream_create`).

---

## Wrapper Spec Created

**File:** `examples/cuda.wrapper_spec`

**Contents:**
- **3 handle types:** `CudaStream`, `CudaEvent`, `CudaDeviceMem`
- **14 functions:** Device management, memory allocation, stream/event creation
- **9 methods:** Stream/event synchronization, timing, queries

**Key Features:**
- Single-line lambda syntax (per torch.wrapper_spec pattern)
- Proper handle types with `drop_fn`
- CUDA C API calls (`cudaStreamCreate`, `cudaMemcpy`, etc.)

**Spec is correct** - the generator is the issue.

---

## What Would Be Needed

### Option A: Fix Wrapper Generator (Recommended)

**Required Changes:**

1. **Fix handle parameter passing:**
   ```rust
   // In generator, when calling lambda with handle params:
   - args.push(format!("{}.inner", param_name));  // WRONG
   + args.push(param_name.clone());               // RIGHT
   ```

2. **Fix method lambda syntax:**
   ```rust
   // For cpp_method with lambdas:
   - format!("h.inner.{}()", lambda_code)  // WRONG
   + format!("{}(h)", lambda_code)          // RIGHT (pass h to lambda)
   // OR just inline the lambda body directly
   ```

3. **Fix function name generation:**
   ```rust
   // Avoid double-prefixing with library name
   - format!("rt_{}_{}", lib_name, func_name)  // If func_name already has lib_name
   + format!("rt_{}", func_name)                // Just add rt_ prefix
   ```

**Estimated Time:** 2-4 hours to fix generator

---

### Option B: Manual C++ Bridge (Not Recommended)

Manually write `bridge.cpp` without using the generator. This violates the SFFI principle that all FFI code should be generated.

**Why Not:**
- Goes against SFFI design philosophy
- Not maintainable (manual edits lost on regeneration)
- User explicitly requested SFFI wrapper generator use

---

### Option C: Wait for PyTorch (Current Approach)

Continue using PyTorch (`lib.torch`) for GPU operations. PyTorch FFI works because:
- Simpler handle types (TorchTensor, TorchStream)
- Methods don't use lambdas (use simple method names like `.cuda()`, `.sync()`)
- No complex handle-to-handle operations

**Trade-offs:**
- ✅ Works today
- ❌ 2GB+ PyTorch dependency
- ❌ Tied to PyTorch API and versioning

---

## Current Status

### What Works (Phases 1-3)

| Phase | Component | Status |
|-------|-----------|--------|
| Phase 1 | PyTorch CUDA Streams | ✅ Complete (via PyTorch FFI) |
| Phase 2 | Context API | ✅ Complete |
| Phase 3 | Async Pipelines | ✅ Complete |

**Total:** ~1,780 lines of working GPU code

### What's Blocked (Phase 4)

| Component | Status | Blocker |
|-----------|--------|---------|
| Direct CUDA FFI | ⚠️ Blocked | Generator bugs #1, #2, #3 |
| Tier 1 (C++ bridge) | ❌ Invalid syntax | Bug #1, #2 |
| Tier 2 (FFI bindings) | ✅ Generated OK | - |
| Tier 3 (Simple API) | ⚠️ Wrong names | Bug #3 |

---

## Recommendation

**Proceed with Phases 1-3 using PyTorch FFI** as complete and production-ready.

**Defer Phase 4** until wrapper generator bugs are fixed.

**Alternative Path:**
If PyTorch dependency is unacceptable, Phase 4 requires either:
1. Generator bug fixes (2-4 hours)
2. Different SFFI approach (manual Rust FFI, not C++ bridge)
3. Pure Simple CUDA bindings (no FFI)

---

## Files Created

| File | Purpose | Status |
|------|---------|--------|
| `examples/cuda.wrapper_spec` | CUDA wrapper specification | ✅ Correct |
| `.build/rust/ffi_cuda/src/bridge.cpp` | Generated C++ bridge | ❌ Has bugs |
| `src/lib/cuda/ffi.spl` | Generated FFI bindings | ✅ Mostly OK |
| `src/lib/cuda/mod.spl` | Generated Simple API | ⚠️ Wrong names |
| `examples/cuda/basic.spl` | CUDA example script | ✅ Written (untested) |

---

## Next Steps

**If continuing with PyTorch (Recommended):**
- ✅ Phases 1-3 are complete and working
- Document PyTorch as the GPU backend
- Phase 4 remains optional future work

**If fixing generator:**
1. File bug report with wrapper generator team
2. Fix bugs #1, #2, #3 in generator source
3. Re-run `bin/simple wrapper-gen examples/cuda.wrapper_spec`
4. Verify generated code compiles and runs
5. Complete Phase 4 with native CUDA

**If manual approach:**
- Would require approval to manually write C++ bridge
- Contradicts SFFI principles
- Not recommended

---

## Conclusion

Phase 4 (Direct CUDA FFI) **cannot be completed** using the SFFI wrapper generator due to critical bugs in lambda code generation. The wrapper spec is correct, but the generator produces invalid C++ syntax.

**Recommendation:** Mark Phases 1-3 as complete (PyTorch-based GPU interface) and defer Phase 4 until generator is fixed.

**What We Have:**
- ✅ Working CUDA streams (via PyTorch)
- ✅ Unified Context API
- ✅ Async pipeline patterns
- ✅ Production-ready GPU code

**What's Blocked:**
- ❌ Native CUDA without PyTorch (blocked by generator)

---

## Related Documents

- `doc/plan/cuda_unified_interface_impl_2026-02-09.md` - Full implementation plan
- `doc/report/cuda_streams_phase1_complete_2026-02-09.md` - Phase 1 report
- `doc/report/context_api_phase2_complete_2026-02-09.md` - Phase 2 report
- `doc/report/async_pipeline_phase3_complete_2026-02-09.md` - Phase 3 report
- `examples/cuda.wrapper_spec` - CUDA wrapper specification (correct)
- `examples/torch.wrapper_spec` - PyTorch wrapper spec (working reference)
