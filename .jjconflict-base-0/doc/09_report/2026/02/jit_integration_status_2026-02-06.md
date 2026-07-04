# JIT Integration Status Report

**Date:** 2026-02-06
**Goal:** Enable JIT compilation to solve autograd value semantics issue

## Current Situation

### What EXISTS (Rust implementations)

1. **JIT Infrastructure** ✅
   - `rust/compiler/src/codegen/jit.rs` - Cranelift JIT compiler
   - `rust/compiler/src/codegen/llvm_jit.rs` - LLVM JIT compiler
   - `rust/compiler/src/codegen/local_execution.rs` - Unified local execution manager
   - `rust/compiler/src/codegen/execution_manager.rs` - ExecutionManager trait

2. **Exec Manager Implementation** ✅
   - `rust/compiler/src/interpreter_extern/exec_manager.rs` - SFFI wrapper functions
   - Functions implemented:
     - `rt_exec_manager_create(backend)` → handle
     - `rt_exec_manager_compile(handle, mir_data)` → error or ""
     - `rt_exec_manager_execute(handle, name, args)` → i64
     - `rt_exec_manager_has_function(handle, name)` → bool
     - `rt_exec_manager_backend_name(handle)` → text
     - `rt_exec_manager_cleanup(handle)`

3. **Simple-Side Wrappers** ✅
   - `src/compiler/execution/mod.spl` - LocalExecutionManager class
   - `src/app/io/mod.spl` - extern fn declarations

4. **Tests** ✅
   - `test/compiler/execution_manager_spec.spl` - SSpec tests

### What's MISSING

1. **Function Registration** ❌
   - `rust/compiler/src/interpreter_extern/mod.rs` doesn't register exec_manager functions
   - Need to add to extern function table

2. **rt_set_jit_backend / rt_get_jit_backend** ❌
   - Declared in Simple but not implemented in Rust
   - Need implementation in exec_manager.rs or separate file

3. **MIR Serialization** ⚠️
   - `parse_mir_from_string()` is placeholder (returns empty module)
   - Need actual MIR deserialization from JSON or binary format

## Blocking Issue: Value Semantics

**Problem:** Autograd backward pass doesn't work because interpreter uses value semantics for arrays.

```simple
var arr = [tensor]
arr[0].apply_gradient(grad)  # Modifies COPY, not original!
```

**Hypothesis:** JIT-compiled code uses reference semantics (compiled mode != interpreter mode)

**Test Needed:**
1. Compile autograd module with JIT
2. Test if gradients propagate correctly
3. If YES → autograd works in compiled mode
4. If NO → value semantics is language-level, need different solution

## Next Steps

### Option A: Minimal Rust Wiring (Recommended)
Register existing implementations - just configuration, not new code:

1. Add function registration in `mod.rs` (~10 lines)
2. Implement `rt_set/get_jit_backend` using existing LocalExecutionManager
3. Test JIT compilation via Simple code
4. Test if autograd works in JIT mode

### Option B: Pure Simple Workaround
Accept interpreter limitation, use global gradient store:

```simple
var GRADIENTS: Dict<i64, TensorF64> = {}

fn backward(t: Tensor):
    # Store gradients globally instead of in Tensor objects
    GRADIENTS[t.id] = compute_gradient(t)
```

### Option C: Accept Limitation
Document that autograd requires compiled mode, focus on other DL features.

## Recommendation

**Try Option A first** - it's mostly wiring existing code, not writing new Rust.
If user prefers "absolutely no Rust changes", fall back to Option B or C.

## File Fixes Made

✅ Fixed `src/compiler/execution/mod.spl` - renamed `auto()` → `auto_select()` (reserved word)
✅ Fixed `test/compiler/execution_manager_spec.spl` - updated method calls

## Auto Issue Found

**Problem:** `auto` is a reserved keyword in Simple parser
**Error:** "expected identifier, found Auto"
**Solution:** Use `auto_select()` instead
