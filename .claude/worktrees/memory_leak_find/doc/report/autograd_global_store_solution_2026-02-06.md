# Autograd Global Store Solution - Pure Simple Workaround

**Date:** 2026-02-06
**Status:** WORKING PROTOTYPE ✅
**Approach:** Option B - Global Gradient Store (Manual State Passing)

## Problem Recap

**Interpreter Value Semantics:**
```simple
var arr = [tensor]
arr[0].apply_gradient(grad)  # Modifies COPY, not original!
```

This blocks standard autograd where tensors store references to input tensors in arrays.

## Solution: Manual State Passing

**Key Insight:** Don't store objects in arrays. Pass state explicitly through function parameters.

## Working Prototype

**File:** `examples/test_autograd_manual.spl`

**Results:**
```
Test 1: Simple Gradient (x * 2.0)
  ✓ SUCCESS! dy/dx = 2.0

Test 2: Chain Rule (x * 2.0 * 3.0)
  ✓ SUCCESS! dz/dx = 6.0

RESULTS: 2/2 tests passed
```

**Method:**
```simple
var values: Dict<i64, TensorF64> = {}
var gradients: Dict<i64, TensorF64> = {}

# Store tensor values, not Tensor objects
values[x_id] = from_data([3.0], [1])

# Compute forward
val y_val = mul_scalar(x_val, 2.0)
values[y_id] = y_val

# Compute gradients
val grad_x = mul_scalar(grad_y, 2.0)
gradients[x_id] = grad_x
```

**Why This Works:**
- No objects in arrays → no value semantics issue
- TensorF64 is concrete data → can be stored directly
- State passed explicitly → no hidden references

## What Was Attempted

### ❌ Attempt 1: Module-Level Mutable Variables
```simple
var GRADIENTS: Dict<i64, TensorF64> = {}  # Doesn't work!
```
**Error:** `variable GRADIENTS not found`
**Reason:** Interpreter doesn't support module-level mutable state

### ❌ Attempt 2: Class Singleton with Module Variable
```simple
var STORE: AutogradStore? = nil  # Also doesn't work!
```
**Error:** Same as above
**Files:** `autograd_global.spl`, `autograd_v2.spl`, `autograd_store.spl`

### ✅ Attempt 3: Manual State Passing
**Works!** Pass Dict parameters explicitly through all functions.

## Path Forward

### Option A: Explicit State API (Simple but Verbose)

```simple
# Create context
var ctx = AutogradContext.create()

# Operations take context
val x = ctx.tensor([3.0], [1], requires_grad: true)
val y = ctx.mul_scalar(x, 2.0)

# Backward with context
ctx.backward(y)

# Get gradients from context
val x_grad = ctx.get_gradient(x.id)
```

**Pros:**
- Works in current interpreter
- Pure Simple solution
- Clear ownership

**Cons:**
- Verbose (must pass ctx everywhere)
- Not ergonomic

### Option B: Wait for Interpreter Fix

Wait for module-level mutable variables support, then use:
```simple
# Global store (when supported)
var GRADIENTS: Dict<i64, TensorF64> = {}

# Clean API
val x = tensor([3.0], requires_grad: true)
val y = x * 2.0
backward(y)
val grad = x.grad()
```

### Option C: Document Limitation

Accept that full autograd requires compiled mode or explicit state passing.

## Recommendation

**Implement Option A** - Explicit Context API

**Rationale:**
1. Works TODAY in pure Simple
2. Provides full autograd functionality
3. Can be refactored later when interpreter improves
4. Other DL code (nn layers, optimizers) can use this

## Implementation Plan

1. ✅ **Prove concept** - Manual state passing works (DONE)
2. **Wrap in Context API** - Create AutogradContext class (~200 lines)
3. **Add operations** - matmul, relu, sum, mean (~150 lines)
4. **Write tests** - Verify all ops work (~100 lines)
5. **Update examples** - Show real usage patterns

**Estimated effort:** 4-6 hours

## Files Created

**Working:**
- `examples/test_autograd_manual.spl` - Proof of concept ✅

**Incomplete (module-level var issue):**
- `src/lib/pure/autograd_global.spl`
- `src/lib/pure/autograd_v2.spl`
- `src/lib/pure/autograd_store.spl`

**Reports:**
- `doc/report/autograd_interpreter_limitation_2026-02-06.md`
- `doc/report/jit_integration_status_2026-02-06.md`
- This file

## Side Discoveries

### Bug Fixed: `auto` Reserved Keyword

**File:** `src/compiler/execution/mod.spl`
**Problem:** `auto()` method name rejected by parser
**Error:** "expected identifier, found Auto"
**Fix:** Renamed to `auto_select()`
**Also fixed:** `test/compiler/execution_manager_spec.spl`

### JIT Integration Status

**Rust Implementation:** ✅ Complete
- `local_execution.rs` - LocalExecutionManager
- `exec_manager.rs` - SFFI wrappers
- `jit.rs`, `llvm_jit.rs` - Backends

**Simple Bindings:** ✅ Declared
- `src/app/io/mod.spl` - extern fn declarations
- `src/compiler/execution/mod.spl` - LocalExecutionManager class

**Missing:** ❌ Function registration
- Need to register rt_exec_manager_* in `mod.rs`
- Need to implement rt_set/get_jit_backend

**Blocker:** Can't test JIT hypothesis without registration

## Next Steps

1. Implement AutogradContext API (Option A)
2. Test with real neural network example
3. If satisfactory → document and move on
4. If not → consider minimal Rust registration for JIT testing

**User chose Option B**, so we're proceeding with pure Simple solution! 🎉
