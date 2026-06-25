# Complete Codegen in Simple with FFI Wrapper

## Proposed Architecture

```
┌─────────────────────────────────────────────┐
│  Full Codegen Logic in Simple              │
│  (codegen.spl - ALL intelligence here)     │
│  - MIR traversal                            │
│  - Type mapping                             │
│  - Instruction selection                    │
│  - Register allocation logic                │
│  - Optimization decisions                   │
│  - Control flow analysis                    │
└─────────────────┬───────────────────────────┘
                  │ FFI calls (complete wrapper)
                  ▼
┌─────────────────────────────────────────────┐
│  Complete FFI Wrapper (Rust)                │
│  - THIN interface layer                     │
│  - Direct Cranelift API mapping             │
│  - No logic, just translation               │
└─────────────────┬───────────────────────────┘
                  │ Cranelift API
                  ▼
┌─────────────────────────────────────────────┐
│  Cranelift Library (External)               │
│  - IR construction                          │
│  - Machine code generation                  │
└─────────────────────────────────────────────┘
```

---

## Current vs Proposed

### Current State

**codegen.spl (662 lines):**
- Pattern matching on MIR instructions ✅
- Type mapping ✅
- Control flow orchestration ✅
- **BUT:** Calls incomplete FFI stubs ❌

**FFI Wrapper (1,160 lines):**
- Module management ✅
- Context management ✅
- **Instruction emission:** STUBS ❌

### Proposed State

**codegen.spl (expand to ~1,500 lines):**
- All MIR instruction handling ✅
- All type conversions ✅
- All optimization decisions ✅
- Register allocation strategy ✅
- **Calls complete FFI wrapper** ✅

**FFI Wrapper (expand to ~2,000 lines):**
- All ~40 instruction FFI functions ✅
- Proper state management ✅
- Complete Cranelift IR emission ✅
- **Pure translation layer** (no logic)

---

## Benefits of This Approach

### ✅ Advantages

1. **Most Logic in Simple**
   - Codegen intelligence is in Simple
   - Easy to modify compilation strategy
   - No Rust knowledge needed for most changes

2. **Clear Separation**
   - Simple: What to generate (strategy)
   - FFI: How to generate (mechanics)
   - Cranelift: Machine code (backend)

3. **Testable in Simple**
   - Can test codegen logic without FFI
   - Can mock FFI layer for testing
   - Easier debugging

4. **Maintainable**
   - Codegen changes = Simple changes
   - FFI wrapper rarely changes
   - Clear boundaries

5. **Still Get Native Performance**
   - Uses Cranelift for optimization
   - JIT and AOT compilation
   - Production-ready output

### ❌ Disadvantages

1. **Still Depends on FFI**
   - Not truly self-hosting
   - Requires Rust runtime
   - Can't compile without Cranelift

2. **FFI Overhead**
   - Function call overhead per instruction
   - Context locking on each call
   - Not as fast as pure Rust or pure Simple

3. **Two Implementations to Maintain**
   - FFI wrapper in Rust (2,000 lines)
   - Codegen logic in Simple (1,500 lines)

4. **Debugging Across Boundary**
   - Harder to debug FFI issues
   - Need to understand both sides

---

## Implementation Plan

### Phase 1: Complete FFI Wrapper (2-3 weeks)

**Expand cranelift_ffi.rs from 1,160 → 2,000 lines**

#### 1.1 State Management (~200 lines)

```rust
struct FuncBuildContext {
    module_handle: i64,
    is_jit: bool,
    ctx: Context,
    func_builder_ctx: FunctionBuilderContext,
    
    // ✅ Add proper builder
    builder: Option<FunctionBuilder<'static>>,
    
    // ✅ Track current state
    current_block: Option<Block>,
    sealed_blocks: HashSet<Block>,
    
    // ✅ Value mapping
    blocks: HashMap<i64, Block>,
    values: HashMap<i64, Value>,
    variables: HashMap<i64, Variable>,
    
    next_block_id: i64,
    next_value_id: i64,
}
```

#### 1.2 Core Arithmetic (~300 lines)

```rust
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_iadd(ctx: i64, a: i64, b: i64) -> i64 {
    emit_binary_op(ctx, a, b, |builder, a, b| builder.ins().iadd(a, b))
}

#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_isub(ctx: i64, a: i64, b: i64) -> i64 {
    emit_binary_op(ctx, a, b, |builder, a, b| builder.ins().isub(a, b))
}

// ... 15 more arithmetic ops
```

#### 1.3 Memory Operations (~400 lines)

```rust
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_load(
    ctx: i64, type_: i64, addr: i64, offset: i64
) -> i64 {
    let mut contexts = FUNC_CONTEXTS.lock().unwrap();
    let fctx = contexts.get_mut(&ctx).unwrap();
    
    let addr_val = fctx.values[&addr];
    let ty = type_from_code(type_);
    
    let mut builder = get_builder(fctx);
    let result = builder.ins().load(
        ty,
        MemFlags::trusted(),
        addr_val,
        offset as i32
    );
    
    store_value(fctx, result)
}

#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_store(
    ctx: i64, value: i64, addr: i64, offset: i64
) {
    let mut contexts = FUNC_CONTEXTS.lock().unwrap();
    let fctx = contexts.get_mut(&ctx).unwrap();
    
    let val = fctx.values[&value];
    let addr_val = fctx.values[&addr];
    
    let mut builder = get_builder(fctx);
    builder.ins().store(
        MemFlags::trusted(),
        val,
        addr_val,
        offset as i32
    );
}
```

#### 1.4 Control Flow (~500 lines)

```rust
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_brif(
    ctx: i64, cond: i64, then_block: i64, else_block: i64
) {
    let mut contexts = FUNC_CONTEXTS.lock().unwrap();
    let fctx = contexts.get_mut(&ctx).unwrap();
    
    let cond_val = fctx.values[&cond];
    let then_bl = fctx.blocks[&then_block];
    let else_bl = fctx.blocks[&else_block];
    
    let mut builder = get_builder(fctx);
    builder.ins().brif(cond_val, then_bl, &[], else_bl, &[]);
}

#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_call(
    ctx: i64, func: i64, args_ptr: i64, args_len: i64
) -> i64 {
    let mut contexts = FUNC_CONTEXTS.lock().unwrap();
    let fctx = contexts.get_mut(&ctx).unwrap();
    
    // Get function reference
    let func_ref = fctx.values[&func];
    
    // Get arguments
    let args_slice = std::slice::from_raw_parts(
        args_ptr as *const i64,
        args_len as usize
    );
    let args: Vec<Value> = args_slice
        .iter()
        .map(|&h| fctx.values[&h])
        .collect();
    
    // Emit call
    let mut builder = get_builder(fctx);
    let inst = builder.ins().call(func_ref, &args);
    let results = builder.inst_results(inst);
    
    if results.is_empty() {
        0
    } else {
        store_value(fctx, results[0])
    }
}
```

#### 1.5 Helper Functions (~600 lines)

```rust
// Common patterns extracted

unsafe fn emit_binary_op<F>(
    ctx: i64,
    a: i64,
    b: i64,
    op: F
) -> i64
where
    F: FnOnce(&mut FunctionBuilder, Value, Value) -> Value
{
    let mut contexts = FUNC_CONTEXTS.lock().unwrap();
    let fctx = contexts.get_mut(&ctx).unwrap();
    
    let val_a = fctx.values[&a];
    let val_b = fctx.values[&b];
    
    let mut builder = get_builder(fctx);
    let result = op(&mut builder, val_a, val_b);
    
    store_value(fctx, result)
}

unsafe fn get_builder(fctx: &mut FuncBuildContext) 
    -> FunctionBuilder<'_> 
{
    FunctionBuilder::new(
        &mut fctx.ctx.func,
        &mut fctx.func_builder_ctx
    )
}

unsafe fn store_value(
    fctx: &mut FuncBuildContext,
    value: Value
) -> i64 {
    let handle = fctx.next_value_id;
    fctx.values.insert(handle, value);
    fctx.next_value_id += 1;
    handle
}
```

**Total FFI Wrapper:** ~2,000 lines

---

### Phase 2: Expand Simple Codegen (1-2 weeks)

**Expand codegen.spl from 662 → 1,500 lines**

#### 2.1 Add More MIR Instructions (~400 lines)

```simple
me compile_inst(inst: MirInst):
    match inst.kind:
        # ... existing cases ...
        
        # ✅ Add array operations
        case ArrayNew(dest, elem_type, len):
            val size = self.type_size(elem_type) * len
            val ptr = cranelift_alloca(self.current_ctx, size)
            self.local_values[dest.id] = ptr
        
        case ArrayGet(dest, array, index):
            val arr_ptr = self.compile_operand(array)
            val idx = self.compile_operand(index)
            val elem_size = self.array_element_size(array.type_)
            val offset = cranelift_imul(self.current_ctx, idx, elem_size)
            val elem_ptr = cranelift_iadd(self.current_ctx, arr_ptr, offset)
            val value = cranelift_load(
                self.current_ctx,
                self.mir_type_to_cl(dest.type_),
                elem_ptr,
                0
            )
            self.local_values[dest.id] = value
        
        # ✅ Add struct operations
        case StructNew(dest, fields):
            val struct_type = dest.type_
            val size = self.type_size(struct_type)
            val ptr = cranelift_alloca(self.current_ctx, size)
            
            var offset = 0
            for (field_idx, field_value) in fields.enumerate():
                val field_val = self.compile_operand(field_value)
                val field_ptr = cranelift_iadd(
                    self.current_ctx,
                    ptr,
                    cranelift_iconst(self.current_ctx, CL_TYPE_I64, offset)
                )
                cranelift_store(self.current_ctx, field_val, field_ptr, 0)
                offset = offset + self.field_size(struct_type, field_idx)
            
            self.local_values[dest.id] = ptr
        
        # ✅ Add more cases for ~30 more instruction types
```

#### 2.2 Enhanced Type System (~200 lines)

```simple
me mir_type_to_cl(type_: MirType) -> i64:
    """Convert MIR type to Cranelift type with full support."""
    match type_.kind:
        case I8: CL_TYPE_I8
        case I16: CL_TYPE_I16
        case I32: CL_TYPE_I32
        case I64: CL_TYPE_I64
        case U8: CL_TYPE_I8
        case U16: CL_TYPE_I16
        case U32: CL_TYPE_I32
        case U64: CL_TYPE_I64
        case F32: CL_TYPE_F32
        case F64: CL_TYPE_F64
        case Bool: CL_TYPE_B1
        
        # ✅ Enhanced pointer handling
        case Ptr(inner, mut_):
            if self.target_ptr_size() == 64:
                CL_TYPE_I64
            else:
                CL_TYPE_I32
        
        # ✅ Enhanced reference handling
        case Ref(inner, mut_):
            CL_TYPE_PTR
        
        # ✅ Handle function pointers
        case FuncPtr(sig):
            CL_TYPE_PTR
        
        # ✅ Handle arrays (as pointers)
        case Array(elem, len):
            CL_TYPE_PTR
        
        # ✅ Handle structs (as aggregates)
        case Struct(fields):
            CL_TYPE_PTR
        
        case _:
            CL_TYPE_I64  # Default

fn type_size(type_: MirType) -> i64:
    """Calculate size in bytes for a type."""
    match type_.kind:
        case I8 | U8 | Bool: 1
        case I16 | U16: 2
        case I32 | U32 | F32: 4
        case I64 | U64 | F64 | Ptr(_, _) | Ref(_, _): 8
        case Array(elem, len):
            self.type_size(elem) * len
        case Struct(fields):
            fields.map(\f: self.type_size(f)).sum()
        case _: 8

fn type_alignment(type_: MirType) -> i64:
    """Calculate alignment for a type."""
    match type_.kind:
        case I8 | U8 | Bool: 1
        case I16 | U16: 2
        case I32 | U32 | F32: 4
        case I64 | U64 | F64 | Ptr(_, _) | Ref(_, _): 8
        case Array(elem, _):
            self.type_alignment(elem)
        case Struct(fields):
            fields.map(\f: self.type_alignment(f)).max() ?? 8
        case _: 8
```

#### 2.3 Optimization Decisions in Simple (~300 lines)

```simple
me should_inline_call(callee: MirFunction) -> bool:
    """Decide whether to inline a function call."""
    # ✅ Inlining strategy in Simple
    if callee.blocks.len() > 10:
        return false  # Too large
    
    if callee.has_loops():
        return false  # Don't inline loops
    
    if callee.instruction_count() < 20:
        return true  # Small functions always inline
    
    false

me optimize_constants() -> bool:
    """Perform constant folding at codegen time."""
    # ✅ Optimization logic in Simple
    var changed = false
    
    for block in self.current_function.blocks:
        for inst in block.instructions:
            match inst.kind:
                case BinOp(dest, Add, Const(a), Const(b)):
                    # Fold constants
                    val result = a + b
                    inst.kind = Const(dest, result)
                    changed = true
                
                case BinOp(dest, Mul, Const(0), _):
                    # Multiply by zero
                    inst.kind = Const(dest, 0)
                    changed = true
                
                # ... more optimization patterns
    
    changed

me select_calling_convention() -> i64:
    """Choose calling convention based on target."""
    match self.target:
        case X86_64:
            if self.is_windows():
                CL_CC_WINDOWS_FASTCALL
            else:
                CL_CC_SYSTEM_V
        case Aarch64:
            CL_CC_SYSTEM_V
        case _:
            CL_CC_SYSTEM_V
```

#### 2.4 Register Allocation Strategy (~200 lines)

```simple
struct RegisterAllocator:
    """Simple register allocation strategy."""
    available_regs: [i64]
    allocated: {LocalId: i64}
    spilled: {LocalId: i64}

impl RegisterAllocator:
    fn allocate_register(local: LocalId) -> i64:
        """Allocate a register or spill to stack."""
        if self.available_regs.is_empty():
            # Spill least recently used
            val spill_local = self.find_lru_local()
            val stack_slot = self.create_stack_slot()
            self.spilled[spill_local] = stack_slot
            val freed_reg = self.allocated[spill_local]
            self.allocated.remove(spill_local)
            self.available_regs.push(freed_reg)
        
        val reg = self.available_regs.pop()
        self.allocated[local] = reg
        reg
    
    fn find_lru_local() -> LocalId:
        """Find least recently used local for spilling."""
        # Simple strategy: just pick first
        self.allocated.keys().first()
```

#### 2.5 Advanced Features (~400 lines)

```simple
# ✅ SIMD support
me compile_simd_op(op: SimdOp):
    match op:
        case VectorAdd(dest, a, b, width):
            # Generate vector add
            pass
        
        case VectorMul(dest, a, b, width):
            # Generate vector multiply
            pass

# ✅ Atomic operations
me compile_atomic(op: AtomicOp):
    match op:
        case AtomicLoad(dest, ptr, ordering):
            val ptr_val = self.compile_operand(ptr)
            val result = cranelift_atomic_load(
                self.current_ctx,
                CL_TYPE_I64,
                ptr_val,
                ordering_to_cl(ordering)
            )
            self.local_values[dest.id] = result
        
        case AtomicStore(ptr, value, ordering):
            val ptr_val = self.compile_operand(ptr)
            val val = self.compile_operand(value)
            cranelift_atomic_store(
                self.current_ctx,
                val,
                ptr_val,
                ordering_to_cl(ordering)
            )

# ✅ Exception handling
me compile_exception(op: ExceptionOp):
    match op:
        case Throw(exception):
            # Unwind stack
            pass
        
        case Catch(handler_block):
            # Set up exception handler
            pass
```

**Total Simple Codegen:** ~1,500 lines

---

## Comparison: Three Approaches

| Aspect | Option A: Pure Simple<br/>(MIR Interpreter) | Option B: FFI Wrapper<br/>(Proposed) | Option C: Pure Rust |
|--------|-------------------------------------|--------------------------------|---------------------|
| **Self-Hosting** | ✅ Yes (pure Simple) | ⚠️ No (needs Rust FFI) | ❌ No (all Rust) |
| **Performance** | ⚠️ Interpreted (slower) | ✅ Native (Cranelift) | ✅ Native (Cranelift) |
| **Lines of Code** | ~1,000 Simple | ~1,500 Simple<br/>~2,000 Rust | ~3,000 Rust |
| **Effort** | 1-2 weeks | 3-4 weeks | 4-6 weeks |
| **Logic Location** | ✅ All in Simple | ✅ Mostly Simple | ❌ All in Rust |
| **Maintainability** | ✅ Easy (one language) | ⚠️ Medium (two languages) | ⚠️ Medium (Rust only) |
| **Dependencies** | ✅ None | ❌ Cranelift (Rust) | ❌ Cranelift (Rust) |
| **Debugging** | ✅ Easy | ⚠️ FFI boundary issues | ⚠️ Complex |
| **JIT/AOT** | ❌ Interpreter only | ✅ Both supported | ✅ Both supported |

---

## Recommended Strategy

### 🎯 Hybrid Timeline

**Phase 1: MIR Interpreter (1-2 weeks)**
- Pure Simple implementation
- Achieve self-hosting
- File: `src/compiler/mir_interpreter.spl` (~1,000 lines)

**Phase 2: Complete FFI Wrapper (2-3 weeks)**
- Complete Rust FFI wrapper
- File: `rust/compiler/src/codegen/cranelift_ffi.rs` (+840 lines)

**Phase 3: Expand Simple Codegen (1-2 weeks)**
- Enhance Simple codegen logic
- File: `src/compiler/codegen.spl` (+840 lines)

**Result:**
- ✅ Self-hosting via interpreter
- ✅ Native performance via FFI
- ✅ Most logic in Simple
- ✅ Best of all worlds

**Total Effort:** 4-7 weeks

---

## Conclusion

**Can we implement full codegen in Simple with FFI wrapper?**

✅ **YES** - Very feasible and actually a good architecture!

**Benefits:**
- Most intelligence in Simple (easy to modify)
- FFI is thin translation layer (rarely changes)
- Get native performance from Cranelift
- Clear separation of concerns

**Drawbacks:**
- Not truly self-hosting (needs Rust FFI)
- More total code than pure interpreter
- Two languages to maintain

**Recommendation:**
1. Start with MIR interpreter (pure Simple, self-hosting)
2. Then add complete FFI codegen (performance)
3. Keep both (interpreter for self-hosting, FFI for production)

This gives you:
- ✅ Self-hosting (interpreter)
- ✅ Performance (FFI + Cranelift)
- ✅ Flexibility (can improve either independently)

