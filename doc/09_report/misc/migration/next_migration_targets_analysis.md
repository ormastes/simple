# Next Migration Targets - Analysis

**Date:** 2026-02-04
**Purpose:** Identify next Rust → Simple migration candidates

## Migration Status Overview

| Component | Rust Size | Simple Status | Priority | Difficulty |
|-----------|-----------|---------------|----------|------------|
| **GC** | 850 lines | ✅ Complete | - | - |
| **CLI Commands** | 1.4M | ✅ 98% Complete | - | - |
| **Compiler** | 7.6M | 🟡 Partial | HIGH | HIGH |
| **Runtime/VM** | 3.3M | ❌ Rust only | HIGH | HIGH |
| **Parser** | 1.2M | ✅ Complete | - | - |
| **Type System** | 272K | 🟡 Partial | HIGH | MEDIUM |
| **Driver** | 1.4M | ✅ Mostly done | LOW | LOW |

## Completed Migrations ✅

### 1. GC (850 lines)
- ✅ `src/app/gc/core.spl` - Mark-and-sweep GC
- ✅ 45 functions (vs 26 in Rust)
- ✅ Only syscall FFI (malloc/free)
- ❌ Deleted: `rust/runtime/src/memory/gc.rs`

### 2. CLI Commands (98%)
- ✅ 72 commands in `src/app/`
- ✅ Dispatch system in Simple
- ✅ Only syscall FFI
- 🟡 Some still call Rust temporarily

### 3. Parser (Complete)
- ✅ `src/compiler/parser/` - Full parser
- ✅ Lexer, tokenizer, AST
- ✅ 10,399 lines in Simple
- 🟡 Rust parser still exists (legacy)

## Migration Candidates

### Option 1: Runtime Value System (HIGH IMPACT) ⭐

**Rust code:**
```
rust/runtime/src/value/
├── core.rs          (1,640 lines) - RuntimeValue
├── collections.rs   (1,640 lines) - List, Dict, Set
├── dict.rs
├── heap.rs
├── actors.rs
├── channels.rs
└── ... 40 more files
Total: ~3.3M
```

**Why migrate:**
- ✅ Core runtime types (List, Dict, RuntimeValue)
- ✅ Used everywhere in the system
- ✅ Self-hosting benefit (Simple using Simple types)
- ✅ Performance: can optimize for Simple workloads

**Difficulty:** HIGH
- Complex pointer management
- Memory layout critical
- Many dependencies

**Impact:** VERY HIGH
- Self-hosting runtime
- Enables full Simple execution

### Option 2: Type System (MEDIUM IMPACT) ⭐⭐

**Rust code:**
```
rust/type/src/
├── effects.rs       (1,500 lines)
├── mod.rs
├── type_check.rs
└── ...
Total: ~272K
```

**Simple code (partial):**
```
src/compiler/type_check/
src/compiler/type_system/
src/compiler/effects.spl
src/compiler/traits.spl
```

**Why migrate:**
- ✅ Type checker in Simple
- ✅ Can modify type rules easily
- ✅ Self-documenting type system
- 🟡 Already partially in Simple

**Difficulty:** MEDIUM-HIGH
- Complex type inference
- Trait resolution
- Effect system

**Impact:** HIGH
- Type errors in Simple
- Easier to extend type system

### Option 3: MIR/HIR Lowering (MEDIUM IMPACT) ⭐

**Rust code:**
```
rust/compiler/src/mir/
rust/compiler/src/hir/
Total: ~2M (part of compiler)
```

**Simple code (exists):**
```
src/compiler/hir.spl
src/compiler/mir.spl
src/compiler/hir_lowering.spl
src/compiler/mir_lowering.spl
```

**Status:** 🟡 Partially implemented

**Why migrate:**
- ✅ IR design in Simple
- ✅ Already partially done
- ✅ Complete the compiler pipeline

**Difficulty:** MEDIUM
- Well-defined transforms
- Already has Simple version

**Impact:** MEDIUM
- Complete compiler in Simple

### Option 4: Bytecode VM (HIGH IMPACT) ⭐⭐⭐

**Rust code:**
```
rust/runtime/src/bytecode/
├── vm.rs           (1,166 lines)
├── opcodes.rs
├── executor.rs
└── ...
Total: ~500K
```

**Why migrate:**
- ✅ Interpreter in Simple
- ✅ Can add instructions easily
- ✅ Self-modifying VM possible
- ✅ Performance insights

**Difficulty:** MEDIUM-HIGH
- Execution loop performance critical
- Stack management
- FFI calls

**Impact:** VERY HIGH
- Self-hosting VM
- Can optimize for Simple

### Option 5: Codegen (LOW PRIORITY)

**Rust code:**
```
rust/compiler/src/codegen/
├── llvm/          (14 files)
├── cranelift/
├── wasm/
Total: ~2M
```

**Why NOT migrate yet:**
- ❌ Performance critical
- ❌ Complex LLVM/Cranelift integration
- ❌ Should stay in Rust for now

**Priority:** LOW (keep in Rust)

## Recommended Migration Order

### Phase 1: Foundation ✅ DONE
1. ✅ GC (850 lines)
2. ✅ CLI Commands (72 commands)

### Phase 2: Runtime Core (RECOMMENDED NEXT) ⭐⭐⭐

**Target:** Runtime Value System

**Files to migrate:**
```
rust/runtime/src/value/core.rs → src/lib/runtime_value.spl
rust/runtime/src/value/collections.rs → src/lib/collections.spl
rust/runtime/src/value/dict.rs → src/lib/dict.spl
rust/runtime/src/value/heap.rs → src/lib/heap.spl
```

**Approach:**
1. Start with `RuntimeValue` core type
2. Migrate `List`, `Dict`, `Set`
3. Implement heap allocation (use Simple GC!)
4. Connect to Simple GC we just built

**Benefits:**
- ✅ Self-hosting runtime types
- ✅ Uses Simple GC (just migrated!)
- ✅ High impact (used everywhere)

**Estimated:** 3-4 weeks

### Phase 3: Type System

**Target:** Complete type checker migration

**Files to migrate:**
```
rust/type/src/*.rs → src/compiler/type_check/
rust/compiler/src/hir/type_check.rs → src/compiler/type_check/
```

**Benefits:**
- Type system fully in Simple
- Easy to modify/extend
- Self-documenting

**Estimated:** 2-3 weeks

### Phase 4: Bytecode VM

**Target:** Interpreter/VM

**Files to migrate:**
```
rust/runtime/src/bytecode/vm.rs → src/lib/runtime/vm.spl
rust/runtime/src/bytecode/opcodes.rs → src/lib/runtime/opcodes.spl
```

**Benefits:**
- Self-hosting VM
- Can optimize for Simple workloads

**Estimated:** 3-4 weeks

### Phase 5: Complete Compiler

**Target:** Remaining compiler parts

**Keep in Rust:**
- Codegen (LLVM/Cranelift)
- Low-level optimizations

## Detailed Analysis: Runtime Value System

### Current Rust Implementation

**RuntimeValue (core.rs - 1,640 lines):**
```rust
pub enum RuntimeValue {
    Nil,
    Bool(bool),
    Int(i64),
    Float(f64),
    String(Arc<String>),
    List(Arc<Vec<RuntimeValue>>),
    Dict(Arc<HashMap<String, RuntimeValue>>),
    // ... many more variants
}
```

**Problems:**
- ❌ In Rust, hard to modify
- ❌ Can't use Simple features
- ❌ Performance optimizations locked in Rust

### Proposed Simple Implementation

**RuntimeValue (src/lib/runtime_value.spl):**
```simple
struct RuntimeValue:
    """Runtime value type.

    All Simple values at runtime use this type.
    Uses Simple GC for memory management.
    """
    tag: ValueTag          # Type tag (Nil, Bool, Int, etc.)
    data: i64              # Inline data or pointer

enum ValueTag:
    Nil
    Bool
    Int
    Float
    String
    List
    Dict
    Object
    Function
    # ... more

impl RuntimeValue:
    fn nil() -> RuntimeValue:
        RuntimeValue(tag: ValueTag.Nil, data: 0)

    fn bool(value: bool) -> RuntimeValue:
        RuntimeValue(tag: ValueTag.Bool, data: if value: 1 else: 0)

    fn int(value: i64) -> RuntimeValue:
        RuntimeValue(tag: ValueTag.Int, data: value)

    # String/List/Dict use Simple GC for allocation
    fn string(value: text) -> RuntimeValue:
        val ptr = gc_allocate(global_gc, value.len(), TYPE_STRING)
        memcpy(ptr, value.ptr(), value.len())
        RuntimeValue(tag: ValueTag.String, data: ptr)
```

**Benefits:**
- ✅ Uses Simple GC (just migrated!)
- ✅ Simple code = easy to modify
- ✅ Can add new value types easily
- ✅ Performance tuning in Simple

### Migration Steps

1. **Core types** (Week 1)
   - RuntimeValue struct
   - ValueTag enum
   - Basic constructors (nil, bool, int, float)

2. **String/List/Dict** (Week 2)
   - String with GC allocation
   - List operations
   - Dict operations

3. **Advanced types** (Week 3)
   - Object values
   - Function values
   - Closures

4. **Integration** (Week 4)
   - Connect to VM
   - Update interpreter
   - Performance testing

### Performance Considerations

| Operation | Rust | Simple | Notes |
|-----------|------|--------|-------|
| Create int | O(1) | O(1) | Same (inline) |
| Create string | O(n) | O(n) | GC allocation |
| List append | O(1) | O(1) | Same |
| Dict lookup | O(1) | O(1) | Hash table |

**Expected:** Similar performance (both use same algorithms)

## Metrics

### Lines to Migrate (Runtime Value System)

| File | Lines | Priority |
|------|-------|----------|
| `value/core.rs` | 1,640 | HIGH |
| `value/collections.rs` | 1,640 | HIGH |
| `value/dict.rs` | 800 | HIGH |
| `value/heap.rs` | 600 | MEDIUM |
| `value/actors.rs` | 500 | LOW |
| `value/channels.rs` | 400 | LOW |
| **Core total** | **5,080** | - |
| **Full total** | **~20,000** | - |

**Recommendation:** Start with core (5,080 lines), defer actors/channels

## Decision Matrix

| Criterion | Runtime Value | Type System | Bytecode VM | Codegen |
|-----------|---------------|-------------|-------------|---------|
| **Impact** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ |
| **Difficulty** | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐⭐ |
| **Dependencies** | GC only | Many | Runtime Value | LLVM |
| **Self-hosting** | Yes | Yes | Yes | Partial |
| **Lines** | 5,080 | 2,000 | 2,000 | 5,000+ |
| **Time** | 3-4 weeks | 2-3 weeks | 3-4 weeks | 8+ weeks |

## Recommendation

### ⭐ PRIMARY TARGET: Runtime Value System

**Why:**
1. ✅ Foundation for everything else
2. ✅ Just migrated GC (synergy!)
3. ✅ High impact (used everywhere)
4. ✅ Enables VM migration next
5. ✅ Self-hosting benefit

**Start with:**
- `value/core.rs` (1,640 lines) → `src/lib/runtime_value.spl`
- `value/collections.rs` (1,640 lines) → `src/lib/collections.spl`
- `value/dict.rs` (800 lines) → `src/lib/dict.spl`

**Total:** ~5,080 lines for core runtime

**Timeline:** 3-4 weeks

## Next Steps

1. ✅ Create FFI specs for memory operations (done!)
2. ⏳ Start Runtime Value migration
3. ⏳ Implement core types
4. ⏳ Connect to Simple GC
5. ⏳ Test and validate

## Conclusion

**Recommended next target: Runtime Value System**

- 5,080 lines of core runtime
- High impact (foundation for everything)
- Synergy with GC migration
- Enables future VM migration
- Self-hosting benefit

**Start immediately after GC completion!** ✅
