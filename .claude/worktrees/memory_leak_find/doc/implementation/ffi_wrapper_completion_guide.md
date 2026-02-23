# FFI Wrapper Completion Guide

**Goal:** Complete the Cranelift FFI wrapper to actually emit IR (not just return IDs)

---

## Problem Analysis

### Current State (Stubs)

```rust
// Example: rt_cranelift_iadd
pub unsafe extern "C" fn rt_cranelift_iadd(ctx: i64, a: i64, b: i64) -> i64 {
    let mut contexts = FUNC_CONTEXTS.lock().unwrap();
    if let Some(fctx) = contexts.get_mut(&ctx) {
        let value_id = fctx.next_value_id;
        fctx.next_value_id += 1;
        value_id  // ⚠️ STUB: Just returns ID, no IR emitted!
    } else {
        0
    }
}
```

**Problem:** No actual Cranelift IR is generated.

### What's Missing

1. **Current block tracking** - Don't know where to insert instructions
2. **Value mapping** - value_id → Cranelift Value mapping not used
3. **FunctionBuilder access** - Can't call `builder.ins().iadd()`
4. **Block switching** - Can't switch between basic blocks

---

## Solution Architecture

### Step 1: Update FuncBuildContext

```rust
struct FuncBuildContext {
    module_handle: i64,
    is_jit: bool,
    ctx: Context,
    func_builder_ctx: FunctionBuilderContext,

    // ✅ ADD THESE:
    current_block: Option<Block>,      // Track current block
    blocks: HashMap<i64, Block>,       // block_id → Cranelift Block
    values: HashMap<i64, Value>,       // value_id → Cranelift Value

    next_block_id: i64,
    next_value_id: i64,
}
```

### Step 2: Helper Function for FunctionBuilder

```rust
/// Get a temporary FunctionBuilder for instruction emission.
///
/// Due to lifetime constraints, we can't store FunctionBuilder in the struct,
/// so we create it on-demand for each instruction.
unsafe fn with_builder<F, R>(fctx: &mut FuncBuildContext, f: F) -> R
where
    F: FnOnce(&mut FunctionBuilder) -> R,
{
    let mut builder = FunctionBuilder::new(
        &mut fctx.ctx.func,
        &mut fctx.func_builder_ctx,
    );

    // Switch to current block if set
    if let Some(block) = fctx.current_block {
        builder.switch_to_block(block);
    }

    f(&mut builder)
}
```

### Step 3: Complete Instruction Implementations

```rust
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_iadd(ctx: i64, a: i64, b: i64) -> i64 {
    let mut contexts = FUNC_CONTEXTS.lock().unwrap();
    if let Some(fctx) = contexts.get_mut(&ctx) {
        // ✅ GET ACTUAL CRANELIFT VALUES
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

        // ✅ EMIT ACTUAL IR
        let result = with_builder(fctx, |builder| {
            builder.ins().iadd(val_a, val_b)
        });

        // ✅ STORE RESULT IN VALUE MAP
        let result_handle = fctx.next_value_id;
        fctx.next_value_id += 1;
        fctx.values.insert(result_handle, result);

        result_handle
    } else {
        0
    }
}
```

### Step 4: Update Block Management

```rust
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_switch_to_block(ctx: i64, block_id: i64) {
    let mut contexts = FUNC_CONTEXTS.lock().unwrap();
    if let Some(fctx) = contexts.get_mut(&ctx) {
        if let Some(&cl_block) = fctx.blocks.get(&block_id) {
            fctx.current_block = Some(cl_block);
        }
    }
}

#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_seal_block(ctx: i64, block_id: i64) {
    let mut contexts = FUNC_CONTEXTS.lock().unwrap();
    if let Some(fctx) = contexts.get_mut(&ctx) {
        if let Some(&cl_block) = fctx.blocks.get(&block_id) {
            with_builder(fctx, |builder| {
                builder.seal_block(cl_block);
            });
        }
    }
}
```

### Step 5: Update Constant Creation

```rust
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_iconst(ctx: i64, type_: i64, value: i64) -> i64 {
    let mut contexts = FUNC_CONTEXTS.lock().unwrap();
    if let Some(fctx) = contexts.get_mut(&ctx) {
        let ty = type_from_code(type_);

        // ✅ EMIT ACTUAL IR
        let cl_value = with_builder(fctx, |builder| {
            builder.ins().iconst(ty, value)
        });

        // ✅ STORE IN VALUE MAP
        let value_handle = fctx.next_value_id;
        fctx.next_value_id += 1;
        fctx.values.insert(value_handle, cl_value);

        value_handle
    } else {
        0
    }
}
```

---

## Implementation Checklist

### Phase 1: Infrastructure (High Priority)

- [ ] Update `FuncBuildContext` struct
  - [ ] Add `current_block: Option<Block>`
  - [ ] Add proper `values` mapping usage
- [ ] Implement `with_builder()` helper
- [ ] Update block management functions
  - [ ] `rt_cranelift_switch_to_block()`
  - [ ] `rt_cranelift_seal_block()`
  - [ ] `rt_cranelift_seal_all_blocks()`

### Phase 2: Constants (High Priority)

- [ ] `rt_cranelift_iconst()` - Integer constants
- [ ] `rt_cranelift_fconst()` - Float constants
- [ ] `rt_cranelift_bconst()` - Boolean constants

### Phase 3: Arithmetic (High Priority)

- [ ] `rt_cranelift_iadd()` - Integer add
- [ ] `rt_cranelift_isub()` - Integer subtract
- [ ] `rt_cranelift_imul()` - Integer multiply
- [ ] `rt_cranelift_sdiv()` - Signed divide
- [ ] `rt_cranelift_udiv()` - Unsigned divide
- [ ] `rt_cranelift_srem()` - Signed remainder
- [ ] `rt_cranelift_urem()` - Unsigned remainder

### Phase 4: Bitwise (Medium Priority)

- [ ] `rt_cranelift_band()` - Bitwise AND
- [ ] `rt_cranelift_bor()` - Bitwise OR
- [ ] `rt_cranelift_bxor()` - Bitwise XOR
- [ ] `rt_cranelift_bnot()` - Bitwise NOT
- [ ] `rt_cranelift_ishl()` - Shift left
- [ ] `rt_cranelift_sshr()` - Signed shift right
- [ ] `rt_cranelift_ushr()` - Unsigned shift right

### Phase 5: Comparison (High Priority)

- [ ] `rt_cranelift_icmp()` - Integer compare
- [ ] `rt_cranelift_fcmp()` - Float compare

### Phase 6: Memory (High Priority)

- [ ] `rt_cranelift_load()` - Load from memory
- [ ] `rt_cranelift_store()` - Store to memory
- [ ] `rt_cranelift_stack_slot()` - Allocate stack slot
- [ ] `rt_cranelift_stack_addr()` - Get stack address
- [ ] `rt_cranelift_get_element_ptr()` - Compute address

### Phase 7: Control Flow (High Priority)

- [ ] `rt_cranelift_br()` - Unconditional branch
- [ ] `rt_cranelift_brif()` - Conditional branch
- [ ] `rt_cranelift_jump()` - Jump to block
- [ ] `rt_cranelift_return()` - Return from function

### Phase 8: Calls (Medium Priority)

- [ ] `rt_cranelift_call()` - Direct call
- [ ] `rt_cranelift_call_indirect()` - Indirect call

### Phase 9: Type Conversion (Medium Priority)

- [ ] `rt_cranelift_bitcast()` - Bitcast
- [ ] `rt_cranelift_sext()` - Sign extend
- [ ] `rt_cranelift_zext()` - Zero extend
- [ ] `rt_cranelift_trunc()` - Truncate

---

## Example Implementations

### Complete Binary Operation Template

```rust
macro_rules! impl_binop_complete {
    ($name:ident, $cranelift_op:ident) => {
        #[no_mangle]
        pub unsafe extern "C" fn $name(ctx: i64, a: i64, b: i64) -> i64 {
            let mut contexts = FUNC_CONTEXTS.lock().unwrap();
            if let Some(fctx) = contexts.get_mut(&ctx) {
                // Get Cranelift values from handles
                let val_a = match fctx.values.get(&a) {
                    Some(v) => *v,
                    None => return 0,
                };
                let val_b = match fctx.values.get(&b) {
                    Some(v) => *v,
                    None => return 0,
                };

                // Emit IR instruction
                let result = with_builder(fctx, |builder| {
                    builder.ins().$cranelift_op(val_a, val_b)
                });

                // Store result
                let result_handle = fctx.next_value_id;
                fctx.next_value_id += 1;
                fctx.values.insert(result_handle, result);

                result_handle
            } else {
                0
            }
        }
    };
}

// Use it:
impl_binop_complete!(rt_cranelift_iadd, iadd);
impl_binop_complete!(rt_cranelift_isub, isub);
impl_binop_complete!(rt_cranelift_imul, imul);
// ... etc
```

### Complete Load Implementation

```rust
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_load(
    ctx: i64,
    type_: i64,
    addr: i64,
    offset: i64,
) -> i64 {
    let mut contexts = FUNC_CONTEXTS.lock().unwrap();
    if let Some(fctx) = contexts.get_mut(&ctx) {
        // Get address value
        let addr_val = match fctx.values.get(&addr) {
            Some(v) => *v,
            None => return 0,
        };

        // Get result type
        let ty = type_from_code(type_);

        // Emit load instruction
        let result = with_builder(fctx, |builder| {
            builder.ins().load(
                ty,
                MemFlags::new(),
                addr_val,
                offset as i32,
            )
        });

        // Store result
        let result_handle = fctx.next_value_id;
        fctx.next_value_id += 1;
        fctx.values.insert(result_handle, result);

        result_handle
    } else {
        0
    }
}
```

### Complete Store Implementation

```rust
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_store(
    ctx: i64,
    value: i64,
    addr: i64,
    offset: i64,
) {
    let mut contexts = FUNC_CONTEXTS.lock().unwrap();
    if let Some(fctx) = contexts.get_mut(&ctx) {
        // Get values
        let val = match fctx.values.get(&value) {
            Some(v) => *v,
            None => return,
        };
        let addr_val = match fctx.values.get(&addr) {
            Some(v) => *v,
            None => return,
        };

        // Emit store instruction
        with_builder(fctx, |builder| {
            builder.ins().store(
                MemFlags::new(),
                val,
                addr_val,
                offset as i32,
            );
        });
    }
}
```

---

## Testing Strategy

### Unit Tests (Per Function)

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_iadd_emits_ir() {
        unsafe {
            // Create module and function context
            let module = rt_cranelift_new_module(
                "test\0".as_ptr() as i64,
                4,
                CL_TARGET_X86_64,
            );

            // ... setup function ...

            // Create constants
            let a = rt_cranelift_iconst(ctx, CL_TYPE_I64, 2);
            let b = rt_cranelift_iconst(ctx, CL_TYPE_I64, 3);

            // Test iadd
            let result = rt_cranelift_iadd(ctx, a, b);

            // Verify result handle is valid
            assert!(result > 0);

            // Verify IR was emitted (check function IR dump)
            // ... verification ...
        }
    }
}
```

### Integration Tests

```rust
#[test]
fn test_simple_function_compilation() {
    // Test: fn add(a: i64, b: i64) -> i64 { a + b }
    unsafe {
        // Create module
        let module = rt_cranelift_new_module(...);

        // Build signature
        let sig = rt_cranelift_signature_new();
        rt_cranelift_signature_add_param(sig, CL_TYPE_I64);
        rt_cranelift_signature_add_param(sig, CL_TYPE_I64);
        rt_cranelift_signature_set_return(sig, CL_TYPE_I64);

        // Begin function
        let ctx = rt_cranelift_begin_function(module, ...);

        // Create entry block
        let entry = rt_cranelift_create_block(ctx);
        rt_cranelift_switch_to_block(ctx, entry);

        // Get parameters
        let param0 = rt_cranelift_get_param(ctx, 0);
        let param1 = rt_cranelift_get_param(ctx, 1);

        // Add parameters
        let result = rt_cranelift_iadd(ctx, param0, param1);

        // Return result
        rt_cranelift_return(ctx, result);

        // End function
        rt_cranelift_end_function(ctx);

        // Verify compilation succeeded
    }
}
```

---

## Effort Estimation

### Time Estimates (Experienced Developer)

| Phase | Functions | Avg Lines/Func | Total Lines | Time |
|-------|-----------|----------------|-------------|------|
| **Infrastructure** | 3 | 30 | 90 | 2 hours |
| **Constants** | 3 | 25 | 75 | 1 hour |
| **Arithmetic** | 7 | 20 | 140 | 2 hours |
| **Bitwise** | 7 | 20 | 140 | 2 hours |
| **Comparison** | 2 | 30 | 60 | 1 hour |
| **Memory** | 5 | 30 | 150 | 3 hours |
| **Control Flow** | 4 | 25 | 100 | 2 hours |
| **Calls** | 2 | 40 | 80 | 2 hours |
| **Type Conversion** | 4 | 25 | 100 | 2 hours |
| **Testing** | - | - | 300 | 4 hours |
| **TOTAL** | **37** | - | **~1,235** | **21 hours** |

**Estimate: 3-4 days of focused work**

---

## Success Criteria

### Functional Tests

- [ ] All 37+ FFI functions implemented
- [ ] All unit tests pass
- [ ] Integration test compiles simple function
- [ ] Generated IR is valid Cranelift IR

### Performance Tests

- [ ] No performance regression vs direct Cranelift use
- [ ] FFI overhead < 5% of total compilation time

### Quality Tests

- [ ] No memory leaks (valgrind clean)
- [ ] No segfaults under normal usage
- [ ] Clear error messages for invalid inputs

---

## Next Steps

1. **Read this guide thoroughly**
2. **Start with Phase 1** (Infrastructure)
   - This unblocks everything else
3. **Implement in order** (Phases 1-9)
   - Don't skip ahead - later phases depend on earlier ones
4. **Test after each phase**
   - Don't accumulate untested code
5. **Update progress** in this document
   - Check off completed items

---

## References

- **Cranelift Book:** https://cranelift.readthedocs.io/
- **InstBuilder API:** https://docs.rs/cranelift-codegen/latest/cranelift_codegen/ir/trait.InstBuilder.html
- **FunctionBuilder:** https://docs.rs/cranelift-frontend/latest/cranelift_frontend/struct.FunctionBuilder.html

---

**Status:** Ready for implementation
**Priority:** High (blocks self-hosting with native performance)
**Complexity:** Medium (straightforward but tedious)
