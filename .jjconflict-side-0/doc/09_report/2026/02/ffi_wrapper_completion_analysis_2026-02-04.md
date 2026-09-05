# FFI Wrapper Analysis: Can We Complete It?

## Current State

**cranelift_ffi.rs** (1,160 lines)
- ✅ Module management (COMPLETE)
- ✅ Function context (COMPLETE)
- ✅ Stack slots (COMPLETE)
- ⚠️ **Instruction emission (INCOMPLETE - mostly stubs)**

---

## What's Missing in FFI Wrapper

### Incomplete Functions (Just Return IDs)

```rust
// These don't actually emit Cranelift IR:

rt_cranelift_iconst()      // ⚠️ Partial - has some code
rt_cranelift_iadd()        // ❌ STUB
rt_cranelift_isub()        // ❌ STUB  
rt_cranelift_imul()        // ❌ STUB
rt_cranelift_sdiv()        // ❌ STUB
rt_cranelift_load()        // ❌ STUB
rt_cranelift_store()       // ❌ STUB (empty!)
rt_cranelift_call()        // ❌ STUB
rt_cranelift_icmp()        // ❌ STUB
rt_cranelift_fcmp()        // ❌ STUB
rt_cranelift_bitcast()     // ❌ STUB
rt_cranelift_jump()        // ❌ STUB
rt_cranelift_brif()        // ❌ STUB
rt_cranelift_return()      // ❌ STUB
# ... and ~30 more
```

---

## Can We Complete the FFI Wrapper?

### ✅ YES - It's Technically Possible

**What we'd need to do:**

For EACH stub function, add Cranelift IR emission like this:

```rust
// BEFORE (stub):
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_iadd(ctx: i64, a: i64, b: i64) -> i64 {
    let mut contexts = FUNC_CONTEXTS.lock().unwrap();
    if let Some(fctx) = contexts.get_mut(&ctx) {
        let value_id = fctx.next_value_id;
        fctx.next_value_id += 1;
        value_id  // ⚠️ Just returns ID!
    } else {
        0
    }
}

// AFTER (complete):
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_iadd(ctx: i64, a: i64, b: i64) -> i64 {
    let mut contexts = FUNC_CONTEXTS.lock().unwrap();
    if let Some(fctx) = contexts.get_mut(&ctx) {
        // Get actual Cranelift values from our value map
        let val_a = match fctx.values.get(&a) {
            Some(v) => *v,
            None => return 0,
        };
        let val_b = match fctx.values.get(&b) {
            Some(v) => *v,
            None => return 0,
        };
        
        // ✅ Actually emit Cranelift IR instruction!
        let mut builder = FunctionBuilder::new(
            &mut fctx.ctx.func,
            &mut fctx.func_builder_ctx
        );
        let result = builder.ins().iadd(val_a, val_b);
        
        // Store result in value map
        let value_id = fctx.next_value_id;
        fctx.values.insert(value_id, result);
        fctx.next_value_id += 1;
        
        value_id
    } else {
        0
    }
}
```

---

## Challenges

### 1. **FunctionBuilder State Management**

**Problem:** Cranelift's `FunctionBuilder` needs to track:
- Current block being built
- Block parameters
- Variable definitions
- Control flow graph

**Current wrapper doesn't maintain this state properly.**

**Solution:**
```rust
struct FuncBuildContext {
    module_handle: i64,
    is_jit: bool,
    ctx: Context,
    func_builder_ctx: FunctionBuilderContext,
    builder: Option<FunctionBuilder<'static>>,  // ✅ Add this
    blocks: HashMap<i64, Block>,
    values: HashMap<i64, Value>,
    current_block: Option<Block>,               // ✅ Add this
    next_block_id: i64,
    next_value_id: i64,
}
```

### 2. **Lifetime Issues**

**Problem:** `FunctionBuilder<'a>` has lifetime tied to function context.

**Solution:** Use unsafe pointers or refactor to build entire function at once.

### 3. **Block Management**

**Problem:** Need to track which block is active for instruction insertion.

**Current code:**
```rust
// Simple calls this, but wrapper doesn't use it:
rt_cranelift_switch_to_block(ctx, block_id)
```

**Fix needed:**
```rust
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_switch_to_block(ctx: i64, block_id: i64) {
    let mut contexts = FUNC_CONTEXTS.lock().unwrap();
    if let Some(fctx) = contexts.get_mut(&ctx) {
        if let Some(&cl_block) = fctx.blocks.get(&block_id) {
            // ✅ Actually switch block in builder
            if let Some(ref mut builder) = fctx.builder {
                builder.switch_to_block(cl_block);
                fctx.current_block = Some(cl_block);
            }
        }
    }
}
```

### 4. **Value Mapping**

**Problem:** Simple uses i64 handles, Cranelift uses `Value` type.

**Current:** Value map exists but isn't used properly.

**Fix:** Properly map handles ↔ Cranelift Values.

---

## Effort Estimation

### Per-Function Implementation

**Simple instruction (iadd, isub, etc.):** ~15-20 lines each
- Get values from map
- Call builder.ins().OPERATION()
- Store result in map

**Complex instruction (call, load, store):** ~30-50 lines each
- Type conversions
- Memory operations
- Multiple operands

**Total Functions to Complete:** ~40 functions

**Estimated Effort:**
- Simple instructions: 20 functions × 20 lines = **400 lines**
- Complex instructions: 20 functions × 40 lines = **800 lines**
- State management refactor: **200 lines**
- Testing and debugging: **500 lines**

**Total:** ~**1,900 lines of Rust code**

**Time:** ~**2-3 weeks** for experienced Rust + Cranelift developer

---

## Alternative Architectures

### Option A: Complete Current FFI Wrapper

**Pros:**
- ✅ Enables native compilation from Simple
- ✅ Full performance (native code)
- ✅ Uses existing Cranelift library

**Cons:**
- ❌ ~2,000 lines of Rust code to write
- ❌ Still depends on Rust Cranelift library
- ❌ Doesn't achieve true self-hosting
- ❌ Complex lifetime management
- ❌ Debugging is difficult (FFI boundary)

**Effort:** 2-3 weeks

---

### Option B: Implement MIR Interpreter in Simple

**Pros:**
- ✅ Pure Simple implementation (no FFI)
- ✅ True self-hosting
- ✅ Simpler to implement
- ✅ Easier to debug
- ✅ No Cranelift dependency

**Cons:**
- ⚠️ Slower execution than native
- ⚠️ Still need native backend for production

**Effort:** 1-2 weeks

**Code:** ~1,000 lines of Simple

---

### Option C: Hybrid Approach

**Phase 1:** MIR interpreter (self-hosting)
- Implement interpreter in Simple
- Achieve compiler running in Simple
- Use for development and testing

**Phase 2:** Complete FFI wrapper (performance)
- Finish Cranelift FFI wrapper
- Use for production builds
- Keep interpreter as fallback

**Total Effort:** 3-5 weeks

---

## Recommendation

### 🎯 **Start with Option B (MIR Interpreter)**

**Why:**
1. **Faster path to self-hosting** (1-2 weeks vs 2-3 weeks)
2. **Pure Simple** (no Rust code to write)
3. **True self-hosting** (no external dependencies)
4. **Simpler implementation** (interpreter vs Cranelift API)
5. **Easier to maintain** (all in Simple)

**Then optionally do Option A** for production performance.

---

## Implementation Plan for Completing FFI Wrapper

**If you choose Option A:**

### Phase 1: State Management (1 week)
1. Add `FunctionBuilder` to context
2. Implement proper block switching
3. Fix value mapping (handle → Cranelift Value)
4. Add current block tracking

### Phase 2: Core Instructions (1 week)
1. Arithmetic: iadd, isub, imul, sdiv, srem
2. Comparisons: icmp, fcmp
3. Bitwise: band, bor, bxor, bnot
4. Shifts: ishl, sshr, ushr

### Phase 3: Memory & Control Flow (1 week)
1. Memory: load, store, alloca
2. Control flow: jump, brif, switch
3. Calls: call, call_indirect
4. Returns: return, return_void

### Phase 4: Testing & Debugging
1. Write test cases for each instruction
2. Debug FFI boundary issues
3. Fix lifetime issues
4. Optimize hot paths

---

## Example: Complete iadd Implementation

```rust
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_iadd(ctx: i64, a: i64, b: i64) -> i64 {
    let mut contexts = FUNC_CONTEXTS.lock().unwrap();
    
    let fctx = match contexts.get_mut(&ctx) {
        Some(c) => c,
        None => return 0,
    };
    
    // Get Cranelift values
    let val_a = match fctx.values.get(&a) {
        Some(v) => *v,
        None => {
            eprintln!("rt_cranelift_iadd: invalid value handle {}", a);
            return 0;
        }
    };
    
    let val_b = match fctx.values.get(&b) {
        Some(v) => *v,
        None => {
            eprintln!("rt_cranelift_iadd: invalid value handle {}", b);
            return 0;
        }
    };
    
    // Get current block
    let current_block = match fctx.current_block {
        Some(b) => b,
        None => {
            eprintln!("rt_cranelift_iadd: no current block");
            return 0;
        }
    };
    
    // Build instruction using FunctionBuilder
    let result = {
        let mut builder = FunctionBuilder::new(
            &mut fctx.ctx.func,
            &mut fctx.func_builder_ctx
        );
        
        builder.switch_to_block(current_block);
        builder.ins().iadd(val_a, val_b)
    };
    
    // Allocate handle for result
    let result_handle = fctx.next_value_id;
    fctx.next_value_id += 1;
    
    // Store in value map
    fctx.values.insert(result_handle, result);
    
    result_handle
}
```

---

## Conclusion

**Can we complete the FFI wrapper?**

✅ **YES** - Technically feasible
- ~1,900 lines of Rust code
- ~2-3 weeks of work
- Requires Cranelift expertise

**Should we?**

⚠️ **Maybe not immediately**
- MIR interpreter is faster path to self-hosting
- Pure Simple implementation is better for self-hosting goals
- FFI wrapper is good for production performance later

**Recommended approach:**
1. ✅ **First:** Implement MIR interpreter in Simple (1-2 weeks)
2. ✅ **Then:** Complete FFI wrapper for performance (2-3 weeks)
3. ✅ **Result:** Best of both worlds

