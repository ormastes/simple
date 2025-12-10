# Codegen Technical Documentation

This document provides detailed technical documentation for Features 99 (Body Block Outlining) and 103 (Codegen Parity Completion) in the Simple Language Compiler.

## Table of Contents

1. [Overview](#overview)
2. [Current Design Rationale](#current-design-rationale)
3. [Feature 99: Body Block Outlining](#feature-99-body-block-outlining)
4. [Feature 103: Codegen Parity Completion](#feature-103-codegen-parity-completion)
5. [Architecture Diagrams](#architecture-diagrams)
6. [Runtime FFI Interface](#runtime-ffi-interface)
7. [Testing Strategy](#testing-strategy)
8. [How to Implement in Another Project](#how-to-implement-in-another-project)

---

## Overview

The Simple Language Compiler uses a hybrid execution model where compilable code is compiled to native machine code via Cranelift, while unsupported features fall back to a tree-walking interpreter. Features 99 and 103 represent critical infrastructure for achieving full native code generation parity between compiled and interpreted execution paths.

### Key Files

| File | Purpose |
|------|---------|
| `src/compiler/src/codegen/cranelift.rs` | AOT Cranelift backend (~2400 lines) |
| `src/compiler/src/codegen/jit.rs` | JIT Cranelift backend |
| `src/compiler/src/codegen/runtime_ffi.rs` | Shared FFI function specs (55+ functions) |
| `src/compiler/src/codegen/types_util.rs` | Type conversion utilities |
| `src/compiler/src/mir/generator.rs` | Generator state machine lowering |
| `src/compiler/src/mir/instructions.rs` | MIR instruction definitions (50+ variants) |
| `src/compiler/src/mir/function.rs` | MIR function and module definitions |
| `src/runtime/src/value/async_gen.rs` | Future and Generator runtime types |

---

## Current Design Rationale

This section explains the key design decisions made in the Simple Language codegen and why they were chosen.

### Why Cranelift?

**Decision**: Use Cranelift as the code generation backend instead of LLVM or custom assembly.

**Rationale**:
- **Fast compile times**: Cranelift is designed for JIT compilation with sub-millisecond function compilation
- **Rust-native**: Written in Rust, easy to integrate without FFI complexity
- **Sufficient optimization**: Provides good optimization without LLVM's compile-time overhead
- **Portable**: Single codebase supports multiple architectures (x86_64, AArch64, etc.)
- **Simpler IR**: Cranelift's IR is closer to machine code than LLVM IR, making it easier to debug

**Trade-offs**:
- Less aggressive optimization than LLVM (acceptable for a scripting language)
- Smaller ecosystem of tools and documentation

### Why a Multi-Stage IR (AST → HIR → MIR)?

**Decision**: Use three intermediate representations before codegen.

```
AST (syntax-focused) → HIR (type-checked) → MIR (lowered, CFG-based) → Machine Code
```

**Rationale**:
- **AST**: Preserves source structure for error messages and IDE tooling
- **HIR**: Allows type checking independent of lowering decisions; supports generics and type inference
- **MIR**: CFG-based IR enables:
  - Effect analysis (async/nogc verification)
  - Liveness analysis (for capture computation)
  - State machine transformation (for generators)
  - Direct mapping to Cranelift's basic block model

**Why not skip HIR?** Type checking on AST is complex with nested expressions. HIR flattens the structure while preserving type information.

**Why not skip MIR?** Cranelift's IR is too low-level for high-level transforms like generator lowering. MIR provides the right abstraction level.

### Why Runtime FFI for Collections?

**Decision**: Implement collections (Array, Tuple, Dict) via runtime FFI calls rather than inline codegen.

**Rationale**:
- **Flexibility**: Runtime can use optimized Rust implementations (Vec, HashMap)
- **GC Integration**: Collections need GC tracking; runtime manages this uniformly
- **Reduced codegen complexity**: One FFI call vs. dozens of inline instructions
- **Polymorphism**: Collections store `RuntimeValue`, not monomorphized types

**Trade-offs**:
- FFI call overhead (~5-10ns per call)
- Acceptable because collection operations are rarely in hot loops
- Future optimization: inline small arrays, specialize common cases

### Why Zero-Cost Abstractions for Closures/Structs?

**Decision**: Implement closures and structs with inline allocation and direct memory access, not FFI.

**Rationale**:
- **Performance**: Field access is a single load instruction (pointer + offset)
- **Predictability**: Compile-time layout computation, no runtime dispatch
- **Compatibility**: Matches C ABI for interop potential

**Implementation**:
```rust
// ClosureCreate: allocate + store fn_ptr + store captures
// Cost: 1 alloc call + N stores

// FieldGet: load from base + offset
// Cost: 1 load instruction (sub-nanosecond)
```

### Why Stackless Generators?

**Decision**: Implement generators as stackless state machines rather than stackful coroutines.

**Rationale**:
- **No stack switching**: Avoids platform-specific assembly for stack manipulation
- **GC-friendly**: All live variables stored in explicit frame slots (visible to GC)
- **Composable**: Generators can be nested without stack depth limits
- **Portable**: Works on all platforms without OS-specific APIs

**Trade-offs**:
- Yield can only appear at the top level of a generator (no yield in nested calls)
- More compiler complexity for state machine transformation

### Why Eager Future Execution?

**Decision**: Current futures execute eagerly at creation time.

**Rationale**:
- **Simpler implementation**: No async runtime scheduler needed
- **Sufficient for effects**: Async annotation still enables effect checking
- **Stepping stone**: Architecture supports lazy execution when scheduler is added

**Future Direction**: Add true async executor for concurrent, non-blocking futures.

### Why Hybrid Compiled/Interpreted Execution?

**Decision**: Support fallback to interpreter for unsupported features.

**Rationale**:
- **Incremental migration**: Add codegen support feature-by-feature
- **Completeness**: All language features work, even if some are slower
- **Debugging**: Interpreter is easier to debug than generated code

**Implementation**:
```rust
MirInst::InterpCall { func_name, args, .. }  // Call interpreter for function
MirInst::InterpEval { expr_index, .. }       // Evaluate expression via interpreter
```

### Why 64-bit Tagged Pointers?

**Decision**: Use 64-bit RuntimeValue with tag bits for type discrimination.

```
┌──────────┬───────────────────────────────────────────┐
│ Tag (3b) │              Payload (61 bits)            │
└──────────┴───────────────────────────────────────────┘
```

**Rationale**:
- **Unboxed primitives**: Integers fit in payload without heap allocation
- **Fast type checks**: Single AND + compare to check type
- **Uniform representation**: All values are 64 bits, simplifies codegen

**Trade-offs**:
- 61-bit integers (not full 64-bit) for tagged representation
- Acceptable because most integers fit in 61 bits

---

## Feature 99: Body Block Outlining

**Importance:** 4/5
**Difficulty:** 4/5
**Status:** COMPLETE

### Goal

Transform Actor/Generator/Future `body_block` references into standalone compiled functions that can be called by the runtime, enabling native execution of async constructs.

### Problem Statement

Actors, generators, and futures in Simple Language have "body blocks" - code blocks that execute asynchronously or lazily. The MIR represents these as:

```rust
// MIR Instructions for async constructs
MirInst::ActorSpawn { dest: VReg, body_block: BlockId }
MirInst::GeneratorCreate { dest: VReg, body_block: BlockId }
MirInst::FutureCreate { dest: VReg, body_block: BlockId }
```

The challenge is that `body_block` is a reference to a block within the parent function. To execute this block in the runtime (possibly on a different thread for actors, or lazily for generators), it must be "outlined" - extracted into a standalone function with its own entry point and captured variables.

### Solution Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                    Parent Function                          │
│  ┌───────────┐    ┌───────────┐    ┌───────────────────┐   │
│  │ Block 0   │───▶│ Block 1   │───▶│ Block 2 (body)    │   │
│  │ (entry)   │    │ setup     │    │ ActorSpawn(b2)    │   │
│  └───────────┘    └───────────┘    └───────────────────┘   │
└─────────────────────────────────────────────────────────────┘
                           │
                           │ Outlining Transform
                           ▼
┌─────────────────────────────────────────────────────────────┐
│                    Outlined Function                        │
│                    (func_outlined_2)                        │
│  ┌───────────────────────────────────────────────────────┐ │
│  │ Entry Block                                            │ │
│  │ 1. Load captures from ctx parameter                    │ │
│  │ 2. Execute body_block instructions                     │ │
│  │ 3. Return (void for actors, value for gen/future)      │ │
│  └───────────────────────────────────────────────────────┘ │
└─────────────────────────────────────────────────────────────┘
```

### Implementation: `expand_with_outlined()`

Location: `src/compiler/src/codegen/cranelift.rs:140-263`

```rust
/// Expand MIR with outlined functions for each body_block use.
fn expand_with_outlined(&self, mir: &MirModule) -> Vec<MirFunction> {
    let mut functions = mir.functions.clone();
    let mut seen = HashSet::new();

    enum BodyKind { Actor, Generator, Future }

    for func in &mir.functions {
        // Compute live-ins for each block (variables used but not defined locally)
        let live_ins_map = func.compute_live_ins();

        for block in &func.blocks {
            for inst in &block.instructions {
                let body_info = match inst {
                    MirInst::ActorSpawn { body_block, .. } => Some((*body_block, BodyKind::Actor)),
                    MirInst::GeneratorCreate { body_block, .. } => Some((*body_block, BodyKind::Generator)),
                    MirInst::FutureCreate { body_block, .. } => Some((*body_block, BodyKind::Future)),
                    _ => None,
                };

                if let Some((body_block, kind)) = body_info {
                    // Create outlined function: clone parent, adjust entry, add ctx param
                    let mut outlined = func.clone();
                    outlined.name = format!("{}_outlined_{}", func.name, body_block.0);
                    outlined.entry_block = body_block;
                    outlined.return_type = match kind {
                        BodyKind::Actor => TypeId::VOID,
                        BodyKind::Generator | BodyKind::Future => TypeId::I64,
                    };

                    // Prune unreachable blocks
                    outlined.retain_reachable_from(body_block);

                    // Add parameter for captured context
                    if kind == BodyKind::Generator {
                        outlined.params.clear();
                        outlined.params.push(MirLocal {
                            name: "generator".to_string(),
                            ty: TypeId::I64,
                            kind: LocalKind::Parameter,
                        });
                    } else {
                        outlined.params.push(MirLocal {
                            name: "ctx".to_string(),
                            ty: TypeId::I64,
                            kind: LocalKind::Parameter,
                        });
                    }

                    // For generators, apply state machine lowering
                    if kind == BodyKind::Generator {
                        let lowered = lower_generator(&outlined, body_block);
                        outlined = lowered.rewritten;
                    }

                    functions.push(outlined);
                }
            }
        }
    }
    functions
}
```

### Capture Buffer Encoding

When outlining a body block, variables from the parent scope that are "live" (used but not defined) in the body must be captured and passed to the outlined function.

#### Capture Flow

```
Parent Function                      Runtime                   Outlined Function
      │                                 │                            │
      │ 1. Pack captures into array     │                            │
      │    rt_array_new(count)          │                            │
      │    rt_array_push(arr, v0)       │                            │
      │    rt_array_push(arr, v1)       │                            │
      │                                 │                            │
      │ 2. Create async construct       │                            │
      │    rt_actor_spawn(body_ptr, ctx)│                            │
      │    ─────────────────────────────▶                            │
      │                                 │ 3. Store ctx, call body    │
      │                                 │    ───────────────────────▶│
      │                                 │                            │
      │                                 │                    4. Load captures
      │                                 │                       rt_array_get(ctx, 0) → v0
      │                                 │                       rt_array_get(ctx, 1) → v1
      │                                 │                            │
      │                                 │                    5. Execute body
      │                                 │                            │
```

#### Codegen for Capture Loading

Location: `src/compiler/src/codegen/cranelift.rs:392-413`

```rust
// If this is an outlined body with captures, load them from ctx (last param)
if let Some(meta) = func.outlined_bodies.get(&func.entry_block) {
    if !meta.live_ins.is_empty() {
        let ctx_param = if func.generator_states.is_some() {
            // For generators, ctx is retrieved via rt_generator_get_ctx
            let gen_param = builder.block_params(entry_block)[0];
            let get_ctx_id = self.runtime_funcs["rt_generator_get_ctx"];
            let get_ctx_ref = self.module.declare_func_in_func(get_ctx_id, builder.func);
            let call = builder.ins().call(get_ctx_ref, &[gen_param]);
            builder.inst_results(call)[0]
        } else {
            // For actors/futures, ctx is the last parameter
            builder.block_params(entry_block)[func.params.len().saturating_sub(1)]
        };

        // Load each captured variable from the ctx array
        let get_id = self.runtime_funcs["rt_array_get"];
        let get_ref = self.module.declare_func_in_func(get_id, builder.func);
        for (idx, reg) in meta.live_ins.iter().enumerate() {
            let idx_val = builder.ins().iconst(types::I64, idx as i64);
            let call = builder.ins().call(get_ref, &[ctx_param, idx_val]);
            let val = builder.inst_results(call)[0];
            vreg_values.insert(*reg, val);
        }
    }
}
```

### OutlinedBody Metadata

Location: `src/compiler/src/mir/function.rs:31-37`

```rust
/// Metadata for an outlined body (actor/generator/future).
#[derive(Debug, Clone)]
pub struct OutlinedBody {
    /// Generated function name (e.g., "main_outlined_2")
    pub name: String,
    /// Virtual registers that must be captured from parent scope
    pub live_ins: Vec<VReg>,
    /// Number of frame slots needed (for generators)
    pub frame_slots: Option<usize>,
}
```

### Liveness Analysis

Location: `src/compiler/src/mir/function.rs:102-166`

The compiler performs standard backward dataflow liveness analysis to determine which variables are "live" at each block entry:

```rust
/// Compute live-in set for each block using standard backward liveness.
pub fn compute_live_ins(&self) -> HashMap<BlockId, HashSet<VReg>> {
    // For each block:
    //   live_in = use ∪ (live_out - def)
    //   live_out = ∪{live_in(succ) | succ ∈ successors(block)}

    // Iterate until fixed point
    while changed {
        for b in &self.blocks {
            // live_out = union of live_in of all successors
            out_set.clear();
            for s in b.terminator.successors() {
                out_set.extend(live_in[s]);
            }

            // live_in = uses ∪ (live_out - defs)
            let mut new_in = block_uses[b.id].clone();
            for reg in &live_out[b.id] {
                if !block_defs[b.id].contains(reg) {
                    new_in.insert(*reg);
                }
            }

            if live_in[b.id] != new_in {
                live_in[b.id] = new_in;
                changed = true;
            }
        }
    }
}
```

---

## Feature 103: Codegen Parity Completion

**Importance:** 5/5
**Difficulty:** 5/5
**Status:** PARTIAL

### Goal

Eliminate interpreter-only stubs and achieve behavioral parity between compiled and interpreted execution across all language features.

### Current Codegen Coverage

#### MIR Instruction Categories

| Category | Instructions | Codegen Status |
|----------|-------------|----------------|
| **Core** | `ConstInt`, `ConstFloat`, `ConstBool`, `Copy`, `BinOp`, `UnaryOp` | ✅ Implemented |
| **Memory** | `Load`, `Store`, `LocalAddr`, `GetElementPtr`, `GcAlloc`, `Wait` | ✅ Implemented |
| **Control** | `Call`, `Jump`, `Branch`, `Return` | ✅ Implemented |
| **Collections** | `ArrayLit`, `TupleLit`, `DictLit`, `IndexGet`, `IndexSet`, `Slice` | ✅ FFI-based |
| **Strings** | `ConstString`, `ConstSymbol`, `FStringFormat` | ✅ FFI-based |
| **Closures** | `ClosureCreate`, `IndirectCall` | ✅ Zero-cost |
| **Objects** | `StructInit`, `FieldGet`, `FieldSet` | ✅ Zero-cost |
| **Methods** | `MethodCallStatic`, `MethodCallVirtual`, `BuiltinMethod` | ✅ Implemented |
| **Patterns** | `PatternTest`, `PatternBind`, `EnumDiscriminant`, `EnumPayload` | ✅ Implemented |
| **Enums** | `EnumUnit`, `EnumWith` | ✅ FFI-based |
| **Async** | `FutureCreate`, `Await`, `ActorSpawn`, `ActorSend`, `ActorRecv` | ✅ Runtime FFI |
| **Generators** | `GeneratorCreate`, `Yield`, `GeneratorNext` | ✅ State Machine |
| **Errors** | `TryUnwrap`, `OptionSome`, `OptionNone`, `ResultOk`, `ResultErr` | ✅ Implemented |
| **Fallback** | `InterpCall`, `InterpEval` | ✅ FFI bridge |

### Implementation Phases

#### Phase 1: Core Instructions (Complete)
Basic computation, memory operations, and control flow.

```rust
// Example: BinOp codegen (cranelift.rs:539-692)
MirInst::BinOp { dest, op, left, right } => {
    let lhs = vreg_values[left];
    let rhs = vreg_values[right];

    let val = match op {
        BinOp::Add => builder.ins().iadd(lhs, rhs),
        BinOp::Sub => builder.ins().isub(lhs, rhs),
        BinOp::Mul => builder.ins().imul(lhs, rhs),
        BinOp::Div => builder.ins().sdiv(lhs, rhs),
        BinOp::Mod => builder.ins().srem(lhs, rhs),
        BinOp::Lt => builder.ins().icmp(IntCC::SignedLessThan, lhs, rhs),
        // ... 15+ more operators
    };
    vreg_values.insert(*dest, val);
}
```

#### Phase 2: Collections (Complete)
Array, tuple, dict operations via runtime FFI.

```rust
// Example: ArrayLit codegen (cranelift.rs:875-903)
MirInst::ArrayLit { dest, elements } => {
    // 1. Create array: rt_array_new(capacity)
    let array_new_id = self.runtime_funcs["rt_array_new"];
    let array_new_ref = self.module.declare_func_in_func(array_new_id, builder.func);
    let capacity = builder.ins().iconst(types::I64, elements.len() as i64);
    let call = builder.ins().call(array_new_ref, &[capacity]);
    let array = builder.inst_results(call)[0];

    // 2. Push each element
    let array_push_id = self.runtime_funcs["rt_array_push"];
    let array_push_ref = self.module.declare_func_in_func(array_push_id, builder.func);

    for elem in elements {
        let elem_val = vreg_values[elem];
        // Wrap as RuntimeValue
        let wrap_call = builder.ins().call(value_int_ref, &[elem_val]);
        let wrapped = builder.inst_results(wrap_call)[0];
        builder.ins().call(array_push_ref, &[array, wrapped]);
    }
    vreg_values.insert(*dest, array);
}
```

#### Phase 3: Closures (Complete - Zero-Cost)

```rust
// ClosureCreate codegen (cranelift.rs:1180-1225)
MirInst::ClosureCreate { dest, func_name, closure_size, capture_offsets, captures, .. } => {
    // Layout: { fn_ptr: *const fn, captures... }

    // 1. Allocate closure struct
    let alloc_id = self.runtime_funcs["rt_alloc"];
    let size_val = builder.ins().iconst(types::I64, *closure_size as i64);
    let call = builder.ins().call(alloc_ref, &[size_val]);
    let closure_ptr = builder.inst_results(call)[0];

    // 2. Store function pointer at offset 0
    let func_id = self.func_ids.get(func_name);
    let func_ref = self.module.declare_func_in_func(func_id, builder.func);
    let fn_addr = builder.ins().func_addr(types::I64, func_ref);
    builder.ins().store(MemFlags::new(), fn_addr, closure_ptr, 0);

    // 3. Store captures at computed byte offsets
    for (i, offset) in capture_offsets.iter().enumerate() {
        let cap_val = vreg_values[&captures[i]];
        builder.ins().store(MemFlags::new(), cap_val, closure_ptr, *offset as i32);
    }

    vreg_values.insert(*dest, closure_ptr);
}
```

#### Phase 4: Objects/Methods (Complete - Zero-Cost)

```rust
// StructInit codegen (cranelift.rs:1287-1323)
MirInst::StructInit { dest, struct_size, field_offsets, field_types, field_values, .. } => {
    // 1. Allocate struct
    let alloc_ref = self.module.declare_func_in_func(alloc_id, builder.func);
    let size_val = builder.ins().iconst(types::I64, *struct_size as i64);
    let call = builder.ins().call(alloc_ref, &[size_val]);
    let ptr = builder.inst_results(call)[0];

    // 2. Store each field at its byte offset (zero-cost pointer arithmetic)
    for (i, (offset, field_type)) in field_offsets.iter().zip(field_types.iter()).enumerate() {
        let field_val = vreg_values[&field_values[i]];
        builder.ins().store(MemFlags::new(), field_val, ptr, *offset as i32);
    }

    vreg_values.insert(*dest, ptr);
}

// FieldGet codegen (cranelift.rs:1325-1343)
MirInst::FieldGet { dest, object, byte_offset, field_type } => {
    // Zero-cost: single load instruction at computed offset
    let obj_ptr = vreg_values[object];
    let cranelift_ty = type_id_to_cranelift(*field_type);
    let val = builder.ins().load(cranelift_ty, MemFlags::new(), obj_ptr, *byte_offset as i32);
    vreg_values.insert(*dest, val);
}
```

#### Phase 5: Pattern Matching (Complete)

```rust
// PatternTest codegen (cranelift.rs:1808-1888)
MirInst::PatternTest { dest, subject, pattern } => {
    let subject_val = vreg_values[subject];

    let result = match pattern {
        MirPattern::Wildcard => builder.ins().iconst(types::I8, 1), // Always matches

        MirPattern::Literal(MirLiteral::Int(n)) => {
            let lit_val = builder.ins().iconst(types::I64, *n);
            builder.ins().icmp(IntCC::Equal, subject_val, lit_val)
        }

        MirPattern::Binding(_) => builder.ins().iconst(types::I8, 1), // Always matches

        MirPattern::Variant { .. } => {
            // Check discriminant via runtime FFI
            let disc_id = self.runtime_funcs["rt_enum_discriminant"];
            let disc_ref = self.module.declare_func_in_func(disc_id, builder.func);
            let call = builder.ins().call(disc_ref, &[subject_val]);
            let disc = builder.inst_results(call)[0];
            // Valid if discriminant != -1
            let neg_one = builder.ins().iconst(types::I64, -1);
            builder.ins().icmp(IntCC::NotEqual, disc, neg_one)
        }
        // ... more patterns
    };
    vreg_values.insert(*dest, result);
}
```

#### Phase 6: Async/Generators (Complete)

##### Generator State Machine Codegen

The generator state machine is the most complex codegen feature. It transforms:

```simple
fn* gen_example():
    yield 1
    yield 2
    return 3
```

Into a dispatcher function:

```
┌─────────────────────────────────────────────────────────────┐
│              Generator Dispatcher Function                  │
├─────────────────────────────────────────────────────────────┤
│  Entry Block (0):                                           │
│    state = rt_generator_get_state(gen)                      │
│    switch(state):                                           │
│      case 0: goto body_start                                │
│      case 1: goto resume_after_yield1                       │
│      case 2: goto resume_after_yield2                       │
│      default: goto completion                               │
├─────────────────────────────────────────────────────────────┤
│  Body Start (2):                                            │
│    v0 = const 1                                             │
│    rt_generator_store_slot(gen, 0, <live vars>)             │
│    rt_generator_set_state(gen, 1)                           │
│    return v0  // yield 1                                    │
├─────────────────────────────────────────────────────────────┤
│  Resume After Yield 1 (3):                                  │
│    <load live vars from slots>                              │
│    v1 = const 2                                             │
│    rt_generator_store_slot(gen, 0, <live vars>)             │
│    rt_generator_set_state(gen, 2)                           │
│    return v1  // yield 2                                    │
├─────────────────────────────────────────────────────────────┤
│  Resume After Yield 2 (4):                                  │
│    <load live vars from slots>                              │
│    v2 = const 3                                             │
│    rt_generator_set_state(gen, 3)                           │
│    rt_generator_mark_done(gen)                              │
│    return v2  // return 3                                   │
├─────────────────────────────────────────────────────────────┤
│  Completion Block (1):                                      │
│    return nil                                               │
└─────────────────────────────────────────────────────────────┘
```

##### MIR Generator Lowering

Location: `src/compiler/src/mir/generator.rs`

```rust
/// Metadata for a single generator state created from a `Yield`.
pub struct GeneratorState {
    /// Monotonic state identifier (0-based).
    pub state_id: u32,
    /// Block that ends with the yield.
    pub yield_block: BlockId,
    /// Block to resume execution at on the next `next()` call.
    pub resume_block: BlockId,
    /// Register holding the yielded value.
    pub yield_value: VReg,
    /// Live registers that must survive across the suspension.
    pub live_after_yield: Vec<VReg>,
}

/// Rewrite a generator body into a state-machine-friendly shape.
pub fn lower_generator(func: &MirFunction, body_block: BlockId) -> GeneratorLowering {
    // 1. Create dispatcher block (0) and completion block (1)
    // 2. Collect reachable blocks from body
    // 3. Compute liveness for frame slot allocation
    // 4. For each Yield instruction:
    //    - Assign state ID
    //    - Create resume block for post-yield instructions
    //    - Record live-after-yield set
    //    - Transform yield into: store frame, set state, return value
    // 5. Return rewritten function with state metadata
}
```

##### Yield Codegen

Location: `src/compiler/src/codegen/cranelift.rs:2155-2184`

```rust
MirInst::Yield { value } => {
    if let Some(state_map) = generator_state_map.as_ref() {
        if let Some(state) = state_map.get(&mir_block.id) {
            let gen_param = builder.block_params(entry_block)[0];

            // 1. Store all live variables into frame slots
            let store_id = self.runtime_funcs["rt_generator_store_slot"];
            let store_ref = self.module.declare_func_in_func(store_id, builder.func);
            for (idx, reg) in state.live_after_yield.iter().enumerate() {
                let val = vreg_values[reg];
                let idx_val = builder.ins().iconst(types::I64, idx as i64);
                builder.ins().call(store_ref, &[gen_param, idx_val, val]);
            }

            // 2. Set next state
            let set_state_id = self.runtime_funcs["rt_generator_set_state"];
            let set_state_ref = self.module.declare_func_in_func(set_state_id, builder.func);
            let next_state = builder.ins().iconst(types::I64, (state.state_id + 1) as i64);
            builder.ins().call(set_state_ref, &[gen_param, next_state]);

            // 3. Return yielded value
            let val = vreg_values[value];
            builder.ins().return_(&[val]);
        }
    }
}
```

##### Generator Dispatcher Codegen

Location: `src/compiler/src/codegen/cranelift.rs:432-486`

```rust
// Generator dispatcher: switch on state and jump to appropriate block
if let Some(states) = &generator_states {
    let generator_param = builder.block_params(entry_block)[0];

    // Load current state
    let get_state_id = self.runtime_funcs["rt_generator_get_state"];
    let get_state_ref = self.module.declare_func_in_func(get_state_id, builder.func);
    let call = builder.ins().call(get_state_ref, &[generator_param]);
    let state_val = builder.inst_results(call)[0];

    // Build dispatch chain: state 0 → body_start, 1 → resume1, 2 → resume2, ...
    let mut targets = Vec::new();
    targets.push(target_block); // state 0 = body start
    for st in states {
        targets.push(*blocks.get(&st.resume_block).unwrap());
    }

    // Emit cascading if-else chain (brif instructions)
    for (idx, tgt) in targets.iter().enumerate() {
        let cmp = builder.ins().icmp_imm(IntCC::Equal, state_val, idx as i64);
        builder.ins().brif(cmp, *tgt, &[], next_block, &[]);
    }
}
```

#### Phase 7: Error Handling (Complete)

```rust
// TryUnwrap codegen (cranelift.rs:2201-2239)
MirInst::TryUnwrap { dest, value, error_block, error_dest } => {
    let val = vreg_values[value];

    // Load discriminant (Option/Result: Some/Ok=1, None/Err=0)
    let disc = builder.ins().load(types::I64, MemFlags::new(), val, 0);
    let zero = builder.ins().iconst(types::I64, 0);
    let is_error = builder.ins().icmp(IntCC::Equal, disc, zero);

    // Branch to error block if None/Err
    let success_block = builder.create_block();
    let err_block = *blocks.get(error_block).unwrap();
    builder.ins().brif(is_error, err_block, &[], success_block, &[]);

    // Success: extract payload (at offset 8)
    builder.switch_to_block(success_block);
    let payload = builder.ins().load(types::I64, MemFlags::new(), val, 8);
    vreg_values.insert(*dest, payload);
}
```

---

## Architecture Diagrams

### Compilation Pipeline

```
Source Code (.spl)
       │
       ▼
   ┌─────────┐
   │  Lexer  │  → Tokens (with INDENT/DEDENT)
   └────┬────┘
        │
        ▼
   ┌─────────┐
   │ Parser  │  → AST
   └────┬────┘
        │
        ▼
   ┌─────────┐
   │   HIR   │  → Type-checked IR
   └────┬────┘
        │
        ▼
   ┌─────────┐
   │   MIR   │  → 50+ instructions with effects
   └────┬────┘
        │
    ┌───┴───────────────────────┐
    │                           │
    ▼                           ▼
┌──────────────┐        ┌───────────────┐
│  Outlining   │        │  Direct Code  │
│  Transform   │        │  Generation   │
│  (Feature 99)│        │               │
└──────┬───────┘        └───────┬───────┘
       │                        │
       ▼                        ▼
┌──────────────┐        ┌───────────────┐
│  Generator   │        │  Cranelift    │
│  Lowering    │        │  Backend      │
│  (#101)      │        │               │
└──────┬───────┘        └───────┬───────┘
       │                        │
       └────────────┬───────────┘
                    │
                    ▼
              ┌─────────┐
              │   SMF   │  → Binary module format
              └────┬────┘
                   │
                   ▼
              ┌─────────┐
              │ Loader  │  → Memory-mapped executable
              └────┬────┘
                   │
                   ▼
              Execution
```

### Runtime FFI Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                      Compiled Code (Cranelift)                  │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌─────────────────┐  ┌─────────────────┐  ┌─────────────────┐ │
│  │ Value Creation  │  │   Collections   │  │  Async/Gen      │ │
│  │                 │  │                 │  │                 │ │
│  │ rt_value_int    │  │ rt_array_new    │  │ rt_actor_spawn  │ │
│  │ rt_value_float  │  │ rt_array_push   │  │ rt_future_new   │ │
│  │ rt_value_bool   │  │ rt_tuple_new    │  │ rt_generator_*  │ │
│  │ rt_value_nil    │  │ rt_dict_new     │  │                 │ │
│  └────────┬────────┘  └────────┬────────┘  └────────┬────────┘ │
│           │                    │                    │          │
└───────────┼────────────────────┼────────────────────┼──────────┘
            │                    │                    │
            ▼                    ▼                    ▼
┌─────────────────────────────────────────────────────────────────┐
│                     Runtime Library (Rust)                      │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌─────────────────────────────────────────────────────────────┐│
│  │  RuntimeValue (64-bit tagged pointer)                       ││
│  │  ┌──────────┬───────────────────────────────────────────┐   ││
│  │  │ Tag (3b) │              Payload (61 bits)            │   ││
│  │  └──────────┴───────────────────────────────────────────┘   ││
│  │                                                             ││
│  │  Tags: INT, FLOAT, BOOL, NIL, HEAP_PTR                      ││
│  └─────────────────────────────────────────────────────────────┘│
│                                                                 │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────────┐ │
│  │ HeapHeader  │  │RuntimeArray │  │ RuntimeGenerator        │ │
│  │             │  │RuntimeTuple │  │ ┌───────────────────┐   │ │
│  │ object_type │  │RuntimeDict  │  │ │ state: u64        │   │ │
│  │ size        │  │RuntimeString│  │ │ slots: Vec<Value> │   │ │
│  │ gc_metadata │  │             │  │ │ ctx: RuntimeValue │   │ │
│  └─────────────┘  └─────────────┘  │ │ body_func: *fn    │   │ │
│                                    │ │ done: bool        │   │ │
│                                    │ └───────────────────┘   │ │
│                                    └─────────────────────────┘ │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## Runtime FFI Interface

Location: `src/compiler/src/codegen/runtime_ffi.rs`

### Function Specification Format

```rust
pub struct RuntimeFuncSpec {
    pub name: &'static str,      // Function name (e.g., "rt_array_new")
    pub params: &'static [Type], // Parameter types
    pub returns: &'static [Type],// Return types (empty for void)
}
```

### Complete FFI Function List

| Category | Function | Signature |
|----------|----------|-----------|
| **Array** | `rt_array_new` | `(i64) -> i64` |
| | `rt_array_push` | `(i64, i64) -> i8` |
| | `rt_array_get` | `(i64, i64) -> i64` |
| | `rt_array_set` | `(i64, i64, i64) -> i8` |
| | `rt_array_pop` | `(i64) -> i64` |
| | `rt_array_clear` | `(i64) -> i8` |
| **Tuple** | `rt_tuple_new` | `(i64) -> i64` |
| | `rt_tuple_set` | `(i64, i64, i64) -> i8` |
| | `rt_tuple_get` | `(i64, i64) -> i64` |
| | `rt_tuple_len` | `(i64) -> i64` |
| **Dict** | `rt_dict_new` | `(i64) -> i64` |
| | `rt_dict_set` | `(i64, i64, i64) -> i8` |
| | `rt_dict_get` | `(i64, i64) -> i64` |
| | `rt_dict_len` | `(i64) -> i64` |
| | `rt_dict_clear` | `(i64) -> i8` |
| | `rt_dict_keys` | `(i64) -> i64` |
| | `rt_dict_values` | `(i64) -> i64` |
| **Index/Slice** | `rt_index_get` | `(i64, i64) -> i64` |
| | `rt_index_set` | `(i64, i64, i64) -> i8` |
| | `rt_slice` | `(i64, i64, i64, i64) -> i64` |
| | `rt_contains` | `(i64, i64) -> i8` |
| **String** | `rt_string_new` | `(i64, i64) -> i64` |
| | `rt_string_concat` | `(i64, i64) -> i64` |
| **Value** | `rt_value_int` | `(i64) -> i64` |
| | `rt_value_float` | `(f64) -> i64` |
| | `rt_value_bool` | `(i8) -> i64` |
| | `rt_value_nil` | `() -> i64` |
| **Object** | `rt_object_new` | `(i32, i32) -> i64` |
| | `rt_object_field_get` | `(i64, i32) -> i64` |
| | `rt_object_field_set` | `(i64, i32, i64) -> i8` |
| **Closure** | `rt_closure_new` | `(i64, i32) -> i64` |
| | `rt_closure_set_capture` | `(i64, i32, i64) -> i8` |
| | `rt_closure_get_capture` | `(i64, i32) -> i64` |
| | `rt_closure_func_ptr` | `(i64) -> i64` |
| **Enum** | `rt_enum_new` | `(i32, i32, i64) -> i64` |
| | `rt_enum_discriminant` | `(i64) -> i64` |
| | `rt_enum_payload` | `(i64) -> i64` |
| **Memory** | `rt_alloc` | `(i64) -> i64` |
| | `rt_free` | `(i64, i64) -> ()` |
| | `rt_ptr_to_value` | `(i64) -> i64` |
| | `rt_value_to_ptr` | `(i64) -> i64` |
| **Async** | `rt_wait` | `(i64) -> i64` |
| | `rt_future_new` | `(i64, i64) -> i64` |
| | `rt_future_await` | `(i64) -> i64` |
| | `rt_actor_spawn` | `(i64, i64) -> i64` |
| | `rt_actor_send` | `(i64, i64) -> ()` |
| | `rt_actor_recv` | `() -> i64` |
| **Generator** | `rt_generator_new` | `(i64, i64, i64) -> i64` |
| | `rt_generator_next` | `(i64) -> i64` |
| | `rt_generator_get_state` | `(i64) -> i64` |
| | `rt_generator_set_state` | `(i64, i64) -> ()` |
| | `rt_generator_store_slot` | `(i64, i64, i64) -> ()` |
| | `rt_generator_load_slot` | `(i64, i64) -> i64` |
| | `rt_generator_get_ctx` | `(i64) -> i64` |
| | `rt_generator_mark_done` | `(i64) -> ()` |
| **Interpreter** | `rt_interp_call` | `(i64, i64, i64) -> i64` |
| | `rt_interp_eval` | `(i64) -> i64` |
| **Error** | `rt_function_not_found` | `(i64, i64) -> i64` |
| | `rt_method_not_found` | `(i64, i64, i64, i64) -> i64` |

---

## Testing Strategy

### Test Coverage by Feature

| Feature | Unit Tests | Integration Tests | System Tests |
|---------|-----------|-------------------|--------------|
| Body Block Outlining | `mir::generator::tests` | Interpreter tests | Runner tests |
| Generator State Machine | `splits_blocks_and_collects_states` | `generator_state_machine_runs_dispatcher` | `runner_generator_*` (9 tests) |
| Future Execution | - | - | `runner_future_*` (5 tests), `runner_async_*` (3 tests) |
| Parity Tests | - | - | `parity_generator_*`, `parity_future_*` |

### Key Test Files

- `src/compiler/src/mir/generator.rs` - MIR transform unit tests
- `src/runtime/src/value/async_gen.rs` - Runtime unit tests
- `src/driver/tests/runner_tests.rs` - System tests

### Parity Testing Strategy

Parity tests ensure compiled code produces the same results as interpreted code:

```rust
// Example parity test structure
#[test]
fn parity_generator_basic_sequence() {
    let source = r#"
fn* counter():
    yield 1
    yield 2
    yield 3

main = fn():
    let gen = counter()
    let a = next(gen)
    let b = next(gen)
    let c = next(gen)
    return a + b + c  // Should be 6
"#;

    // Run via interpreter
    let interp_result = run_interpreted(source);

    // Run via compiled code
    let compiled_result = run_compiled(source);

    assert_eq!(interp_result, compiled_result);
}
```

---

## Remaining Gaps and Future Work

### Feature 103 Gaps

1. **True Async Executor**: Current futures execute eagerly. Need async runtime integration for non-blocking execution.

2. **GC Safety Across Yields**: Generator frame slots store `RuntimeValue` but lack proper GC root registration between yields.

3. **Complex Pattern Matching**: Tuple, struct, or patterns, and guard patterns have limited codegen support.

4. **Inline Await in Generators**: Combining `await` inside generator bodies is not yet supported.

### Performance Optimization Opportunities

1. **Escape Analysis**: Avoid heap allocation for objects that don't escape function scope.

2. **Inline Caching**: Cache method lookups for virtual dispatch.

3. **Register Allocation**: Current naive allocation could be improved with graph coloring.

4. **Loop Optimizations**: Add support for loop invariant code motion and strength reduction.

---

## How to Implement in Another Project

This section provides a step-by-step guide for implementing a similar codegen system in a different compiler project.

### Prerequisites

Before starting, you need:
1. A parser that produces an AST
2. A type system (can be simple or complex)
3. Understanding of your target language's semantics

### Step 1: Define Your IR Hierarchy

Design your intermediate representations. The Simple Language uses three stages:

```
┌─────────────────────────────────────────────────────────────────────┐
│                           IR Design                                  │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│  1. AST (Abstract Syntax Tree)                                       │
│     - Mirrors source syntax                                          │
│     - Nodes: Statement, Expression, Declaration, etc.                │
│     - Purpose: Parsing, error reporting, syntax highlighting         │
│                                                                      │
│  2. HIR (High-level IR)                                              │
│     - Type-annotated expressions                                     │
│     - Desugared constructs (for loops → while loops)                 │
│     - Purpose: Type checking, trait resolution, generics             │
│                                                                      │
│  3. MIR (Mid-level IR)                                               │
│     - Control flow graph (CFG) with basic blocks                     │
│     - SSA-like virtual registers                                     │
│     - Explicit instructions (no nested expressions)                  │
│     - Purpose: Optimization, analysis, codegen                       │
│                                                                      │
└─────────────────────────────────────────────────────────────────────┘
```

#### Minimal MIR Definition

```rust
// Basic block identifier
pub struct BlockId(pub u32);

// Virtual register (SSA-style value)
pub struct VReg(pub u32);

// Basic block with instructions and terminator
pub struct BasicBlock {
    pub id: BlockId,
    pub instructions: Vec<Instruction>,
    pub terminator: Terminator,
}

// Block terminator (control flow)
pub enum Terminator {
    Return(Option<VReg>),
    Jump(BlockId),
    Branch { cond: VReg, then_block: BlockId, else_block: BlockId },
    Unreachable,
}

// Instructions - start simple, add more as needed
pub enum Instruction {
    // Constants
    ConstInt { dest: VReg, value: i64 },
    ConstFloat { dest: VReg, value: f64 },
    ConstBool { dest: VReg, value: bool },

    // Operations
    BinOp { dest: VReg, op: BinOp, left: VReg, right: VReg },
    UnaryOp { dest: VReg, op: UnaryOp, operand: VReg },

    // Control
    Call { dest: Option<VReg>, func: String, args: Vec<VReg> },

    // Memory (add later)
    Load { dest: VReg, addr: VReg },
    Store { addr: VReg, value: VReg },
}

// Function definition
pub struct Function {
    pub name: String,
    pub params: Vec<(String, Type)>,
    pub return_type: Type,
    pub blocks: Vec<BasicBlock>,
    pub entry_block: BlockId,
}
```

### Step 2: Set Up Cranelift

Add Cranelift dependencies to your project:

```toml
# Cargo.toml
[dependencies]
cranelift-codegen = "0.111"      # Core codegen
cranelift-frontend = "0.111"     # SSA builder helpers
cranelift-module = "0.111"       # Module/linking support
cranelift-object = "0.111"       # Object file emission
cranelift-jit = "0.111"          # Optional: JIT compilation
target-lexicon = "0.12"          # Target triple handling
```

#### Basic Cranelift Setup

```rust
use cranelift_codegen::ir::{AbiParam, Function, Signature, types};
use cranelift_codegen::isa::CallConv;
use cranelift_codegen::settings::{self, Configurable};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{DataDescription, Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};

pub struct Codegen {
    module: ObjectModule,
    ctx: cranelift_codegen::Context,
    func_ctx: FunctionBuilderContext,
}

impl Codegen {
    pub fn new() -> Self {
        // 1. Configure settings
        let mut flag_builder = settings::builder();
        flag_builder.set("opt_level", "speed").unwrap();
        let flags = settings::Flags::new(flag_builder);

        // 2. Create target ISA
        let isa_builder = cranelift_native::builder().unwrap();
        let isa = isa_builder.finish(flags).unwrap();

        // 3. Create module
        let builder = ObjectBuilder::new(
            isa,
            "my_module",
            cranelift_module::default_libcall_names(),
        ).unwrap();
        let module = ObjectModule::new(builder);

        Self {
            module,
            ctx: cranelift_codegen::Context::new(),
            func_ctx: FunctionBuilderContext::new(),
        }
    }
}
```

### Step 3: Implement Basic Codegen

Start with the simplest possible function: returning a constant.

```rust
impl Codegen {
    /// Compile a function that returns a constant integer.
    pub fn compile_const_function(&mut self, name: &str, value: i64) -> Result<(), String> {
        // 1. Create function signature: fn() -> i64
        let mut sig = self.module.make_signature();
        sig.returns.push(AbiParam::new(types::I64));

        // 2. Declare function in module
        let func_id = self.module
            .declare_function(name, Linkage::Export, &sig)
            .map_err(|e| e.to_string())?;

        // 3. Set up function context
        self.ctx.func.signature = sig;
        self.ctx.func.name = cranelift_codegen::ir::UserFuncName::user(0, func_id.as_u32());

        // 4. Build function body
        let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.func_ctx);

        // Create entry block
        let entry_block = builder.create_block();
        builder.append_block_params_for_function_params(entry_block);
        builder.switch_to_block(entry_block);
        builder.seal_block(entry_block);

        // Generate: return constant
        let const_val = builder.ins().iconst(types::I64, value);
        builder.ins().return_(&[const_val]);

        builder.finalize();

        // 5. Define function
        self.module
            .define_function(func_id, &mut self.ctx)
            .map_err(|e| e.to_string())?;

        // 6. Clear context for next function
        self.module.clear_context(&mut self.ctx);

        Ok(())
    }
}
```

### Step 4: Implement MIR → Cranelift Translation

Now connect your MIR to Cranelift:

```rust
impl Codegen {
    pub fn compile_function(&mut self, func: &Function) -> Result<(), String> {
        // 1. Create signature from function params/return
        let mut sig = self.module.make_signature();
        for (_name, ty) in &func.params {
            sig.params.push(AbiParam::new(type_to_cranelift(ty)));
        }
        if func.return_type != Type::Void {
            sig.returns.push(AbiParam::new(type_to_cranelift(&func.return_type)));
        }

        // 2. Declare function
        let func_id = self.module
            .declare_function(&func.name, Linkage::Export, &sig)
            .map_err(|e| e.to_string())?;

        self.ctx.func.signature = sig;

        // 3. Build function
        let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.func_ctx);

        // Create Cranelift blocks for each MIR block
        let mut blocks: HashMap<BlockId, cranelift_codegen::ir::Block> = HashMap::new();
        for mir_block in &func.blocks {
            let cl_block = builder.create_block();
            blocks.insert(mir_block.id, cl_block);
        }

        // Map virtual registers to Cranelift values
        let mut vreg_values: HashMap<VReg, cranelift_codegen::ir::Value> = HashMap::new();

        // Set up entry block with parameters
        let entry_block = blocks[&func.entry_block];
        builder.append_block_params_for_function_params(entry_block);
        builder.switch_to_block(entry_block);

        // Map function parameters to vregs
        for (i, (name, _ty)) in func.params.iter().enumerate() {
            let param_val = builder.block_params(entry_block)[i];
            // Assume params are VReg(0), VReg(1), etc.
            vreg_values.insert(VReg(i as u32), param_val);
        }

        // 4. Compile each block
        for mir_block in &func.blocks {
            let cl_block = blocks[&mir_block.id];
            builder.switch_to_block(cl_block);

            // Compile instructions
            for inst in &mir_block.instructions {
                self.compile_instruction(inst, &mut builder, &mut vreg_values)?;
            }

            // Compile terminator
            self.compile_terminator(&mir_block.terminator, &mut builder, &vreg_values, &blocks)?;
        }

        // 5. Seal all blocks and finalize
        for mir_block in &func.blocks {
            builder.seal_block(blocks[&mir_block.id]);
        }
        builder.finalize();

        // 6. Define function
        self.module.define_function(func_id, &mut self.ctx)?;
        self.module.clear_context(&mut self.ctx);

        Ok(())
    }

    fn compile_instruction(
        &self,
        inst: &Instruction,
        builder: &mut FunctionBuilder,
        vreg_values: &mut HashMap<VReg, cranelift_codegen::ir::Value>,
    ) -> Result<(), String> {
        match inst {
            Instruction::ConstInt { dest, value } => {
                let val = builder.ins().iconst(types::I64, *value);
                vreg_values.insert(*dest, val);
            }

            Instruction::ConstFloat { dest, value } => {
                let val = builder.ins().f64const(*value);
                vreg_values.insert(*dest, val);
            }

            Instruction::ConstBool { dest, value } => {
                let val = builder.ins().iconst(types::I8, if *value { 1 } else { 0 });
                vreg_values.insert(*dest, val);
            }

            Instruction::BinOp { dest, op, left, right } => {
                let lhs = vreg_values[left];
                let rhs = vreg_values[right];

                let result = match op {
                    BinOp::Add => builder.ins().iadd(lhs, rhs),
                    BinOp::Sub => builder.ins().isub(lhs, rhs),
                    BinOp::Mul => builder.ins().imul(lhs, rhs),
                    BinOp::Div => builder.ins().sdiv(lhs, rhs),
                    BinOp::Lt => {
                        let cmp = builder.ins().icmp(
                            cranelift_codegen::ir::condcodes::IntCC::SignedLessThan,
                            lhs, rhs
                        );
                        builder.ins().uextend(types::I64, cmp)
                    }
                    // Add more operators as needed
                };
                vreg_values.insert(*dest, result);
            }

            Instruction::Call { dest, func, args } => {
                // Look up function, call it, store result
                // (Implementation depends on your function registry)
                todo!("Implement function calls");
            }

            _ => todo!("Implement other instructions"),
        }
        Ok(())
    }

    fn compile_terminator(
        &self,
        term: &Terminator,
        builder: &mut FunctionBuilder,
        vreg_values: &HashMap<VReg, cranelift_codegen::ir::Value>,
        blocks: &HashMap<BlockId, cranelift_codegen::ir::Block>,
    ) -> Result<(), String> {
        match term {
            Terminator::Return(None) => {
                builder.ins().return_(&[]);
            }

            Terminator::Return(Some(val)) => {
                let ret_val = vreg_values[val];
                builder.ins().return_(&[ret_val]);
            }

            Terminator::Jump(target) => {
                let target_block = blocks[target];
                builder.ins().jump(target_block, &[]);
            }

            Terminator::Branch { cond, then_block, else_block } => {
                let cond_val = vreg_values[cond];
                let then_bl = blocks[then_block];
                let else_bl = blocks[else_block];
                builder.ins().brif(cond_val, then_bl, &[], else_bl, &[]);
            }

            Terminator::Unreachable => {
                builder.ins().trap(cranelift_codegen::ir::TrapCode::unwrap_user(1));
            }
        }
        Ok(())
    }
}

fn type_to_cranelift(ty: &Type) -> types::Type {
    match ty {
        Type::I64 => types::I64,
        Type::F64 => types::F64,
        Type::Bool => types::I8,
        Type::Void => types::I64, // Use I64 for void ABI
        _ => types::I64, // Default to pointer-sized
    }
}
```

### Step 5: Implement Runtime FFI

For complex operations, define runtime functions in Rust and call them from generated code:

```rust
// runtime/src/lib.rs
#[no_mangle]
pub extern "C" fn rt_array_new(capacity: i64) -> *mut Vec<i64> {
    let v = Vec::with_capacity(capacity as usize);
    Box::into_raw(Box::new(v))
}

#[no_mangle]
pub extern "C" fn rt_array_push(arr: *mut Vec<i64>, value: i64) {
    unsafe {
        (*arr).push(value);
    }
}

#[no_mangle]
pub extern "C" fn rt_array_get(arr: *mut Vec<i64>, index: i64) -> i64 {
    unsafe {
        (*arr).get(index as usize).copied().unwrap_or(0)
    }
}
```

Register FFI functions in codegen:

```rust
impl Codegen {
    fn register_runtime_functions(&mut self) -> HashMap<String, FuncId> {
        let mut funcs = HashMap::new();

        // rt_array_new: (i64) -> i64
        let mut sig = self.module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let id = self.module.declare_function(
            "rt_array_new",
            Linkage::Import,
            &sig
        ).unwrap();
        funcs.insert("rt_array_new".to_string(), id);

        // Add more runtime functions...

        funcs
    }

    fn call_runtime(
        &self,
        name: &str,
        args: &[cranelift_codegen::ir::Value],
        builder: &mut FunctionBuilder,
        runtime_funcs: &HashMap<String, FuncId>,
    ) -> cranelift_codegen::ir::Value {
        let func_id = runtime_funcs[name];
        let func_ref = self.module.declare_func_in_func(func_id, builder.func);
        let call = builder.ins().call(func_ref, args);
        builder.inst_results(call)[0]
    }
}
```

### Step 6: Implement Body Block Outlining

For async constructs (futures, generators, actors), implement outlining:

```rust
impl Codegen {
    /// Extract a block into a standalone function.
    fn outline_block(
        &self,
        parent: &Function,
        body_block: BlockId,
        live_ins: &[VReg],
    ) -> Function {
        // 1. Create new function
        let mut outlined = Function {
            name: format!("{}_outlined_{}", parent.name, body_block.0),
            params: vec![("ctx".to_string(), Type::Ptr)], // Context parameter
            return_type: Type::I64,
            blocks: vec![],
            entry_block: body_block,
        };

        // 2. Copy only reachable blocks from body_block
        let reachable = self.compute_reachable(parent, body_block);
        for block in &parent.blocks {
            if reachable.contains(&block.id) {
                outlined.blocks.push(block.clone());
            }
        }

        // 3. Add capture-loading prologue to entry block
        let entry = outlined.blocks.iter_mut()
            .find(|b| b.id == body_block)
            .unwrap();

        // Insert loads from ctx array at the beginning
        let mut prologue = Vec::new();
        for (idx, vreg) in live_ins.iter().enumerate() {
            prologue.push(Instruction::RuntimeCall {
                dest: Some(*vreg),
                func: "rt_array_get".to_string(),
                args: vec![VReg(0), VReg::constant(idx as i64)], // ctx, index
            });
        }
        prologue.append(&mut entry.instructions);
        entry.instructions = prologue;

        outlined
    }

    fn compute_reachable(&self, func: &Function, start: BlockId) -> HashSet<BlockId> {
        let mut reachable = HashSet::new();
        let mut stack = vec![start];

        while let Some(id) = stack.pop() {
            if !reachable.insert(id) {
                continue;
            }
            if let Some(block) = func.blocks.iter().find(|b| b.id == id) {
                for succ in block.terminator.successors() {
                    stack.push(succ);
                }
            }
        }
        reachable
    }
}
```

### Step 7: Implement Generator State Machine

The most complex part - transform generators into state machines:

```rust
/// Generator state machine transformation.
pub struct GeneratorLowering {
    pub rewritten: Function,
    pub states: Vec<GeneratorState>,
}

pub struct GeneratorState {
    pub state_id: u32,
    pub yield_block: BlockId,
    pub resume_block: BlockId,
    pub live_after_yield: Vec<VReg>,
}

pub fn lower_generator(func: &Function, body_block: BlockId) -> GeneratorLowering {
    let mut rewritten = func.clone();
    let mut states = Vec::new();
    let mut state_id = 0;

    // 1. Find all Yield instructions
    for block in &func.blocks {
        for (inst_idx, inst) in block.instructions.iter().enumerate() {
            if let Instruction::Yield { value } = inst {
                // Compute live variables after this yield
                let live_after = compute_live_at(func, block.id, inst_idx + 1);

                // Create resume block for instructions after yield
                let resume_block = split_block_after(&mut rewritten, block.id, inst_idx);

                states.push(GeneratorState {
                    state_id,
                    yield_block: block.id,
                    resume_block,
                    live_after_yield: live_after,
                });

                state_id += 1;
            }
        }
    }

    // 2. Create dispatcher block at entry
    let dispatcher = create_dispatcher(&mut rewritten, body_block, &states);
    rewritten.entry_block = dispatcher;

    // 3. Create completion block
    let completion = create_completion_block(&mut rewritten);

    // 4. Transform each Yield into: save state, return value
    for state in &states {
        transform_yield(&mut rewritten, state);
    }

    GeneratorLowering { rewritten, states }
}

fn create_dispatcher(
    func: &mut Function,
    body_start: BlockId,
    states: &[GeneratorState],
) -> BlockId {
    let dispatcher_id = func.new_block();
    let dispatcher = func.block_mut(dispatcher_id).unwrap();

    // gen_param = parameter 0 (the generator object)
    // state = rt_generator_get_state(gen_param)
    dispatcher.instructions.push(Instruction::RuntimeCall {
        dest: Some(VReg::STATE),
        func: "rt_generator_get_state".to_string(),
        args: vec![VReg::GEN_PARAM],
    });

    // Switch on state: 0 → body_start, 1 → resume_1, 2 → resume_2, ...
    // (Implemented as chain of conditional branches)

    dispatcher_id
}

fn transform_yield(func: &mut Function, state: &GeneratorState) {
    let block = func.block_mut(state.yield_block).unwrap();

    // Find and replace Yield instruction with:
    // 1. Store live variables to frame slots
    // 2. Set next state
    // 3. Return yielded value

    let mut new_instructions = Vec::new();

    for inst in &block.instructions {
        if let Instruction::Yield { value } = inst {
            // Store each live variable
            for (idx, vreg) in state.live_after_yield.iter().enumerate() {
                new_instructions.push(Instruction::RuntimeCall {
                    dest: None,
                    func: "rt_generator_store_slot".to_string(),
                    args: vec![VReg::GEN_PARAM, VReg::constant(idx as i64), *vreg],
                });
            }

            // Set next state
            new_instructions.push(Instruction::RuntimeCall {
                dest: None,
                func: "rt_generator_set_state".to_string(),
                args: vec![VReg::GEN_PARAM, VReg::constant((state.state_id + 1) as i64)],
            });

            // Return yielded value
            block.terminator = Terminator::Return(Some(*value));
        } else {
            new_instructions.push(inst.clone());
        }
    }

    block.instructions = new_instructions;
}
```

### Step 8: Emit and Link

Finally, emit the object file and link:

```rust
impl Codegen {
    /// Emit object file
    pub fn emit_object(self) -> Vec<u8> {
        let product = self.module.finish();
        product.emit().unwrap()
    }

    /// Write to file
    pub fn write_object(&self, path: &str) -> Result<(), std::io::Error> {
        let bytes = self.emit_object();
        std::fs::write(path, bytes)
    }
}

// Linking (using system linker)
fn link_executable(object_path: &str, output_path: &str, runtime_lib: &str) {
    std::process::Command::new("cc")
        .args(&[
            object_path,
            "-o", output_path,
            "-L", "path/to/runtime",
            "-l", runtime_lib,
        ])
        .status()
        .expect("Failed to link");
}
```

### Complete Implementation Checklist

```
□ Phase 1: Basic Infrastructure
  □ Define MIR data structures (blocks, instructions, terminators)
  □ Set up Cranelift module and context
  □ Implement type conversion (your types → Cranelift types)
  □ Compile a function that returns a constant

□ Phase 2: Core Instructions
  □ ConstInt, ConstFloat, ConstBool
  □ BinOp (arithmetic, comparison)
  □ UnaryOp (negation, not)
  □ Copy (register to register)

□ Phase 3: Control Flow
  □ Jump (unconditional branch)
  □ Branch (conditional branch)
  □ Return (with/without value)
  □ Block parameter passing (phi nodes)

□ Phase 4: Function Calls
  □ Direct function calls
  □ Register function signatures
  □ Handle return values

□ Phase 5: Runtime FFI
  □ Define runtime functions in Rust
  □ Import runtime functions in Cranelift
  □ Implement collection operations (array, tuple, dict)

□ Phase 6: Memory Operations
  □ Load/Store instructions
  □ Stack allocation for locals
  □ Heap allocation (GC integration)

□ Phase 7: Closures
  □ ClosureCreate (allocate + store fn_ptr + captures)
  □ IndirectCall (load fn_ptr + call)
  □ Capture loading

□ Phase 8: Objects/Structs
  □ StructInit (allocate + store fields)
  □ FieldGet (load at offset)
  □ FieldSet (store at offset)

□ Phase 9: Outlining (for async constructs)
  □ Compute live-ins via liveness analysis
  □ Create outlined functions from blocks
  □ Pack/unpack captures via ctx array

□ Phase 10: Generators
  □ Discover yield points
  □ Compute live-after-yield sets
  □ Create dispatcher block
  □ Transform yields into state saves + returns
  □ Implement resume logic

□ Phase 11: Testing & Parity
  □ Unit tests for each instruction type
  □ Integration tests for function calls
  □ System tests for full programs
  □ Parity tests (compiled vs. interpreted)
```

### Common Pitfalls and Solutions

| Problem | Symptom | Solution |
|---------|---------|----------|
| Block not sealed | Cranelift panic: "block not sealed" | Call `builder.seal_block()` after all predecessors are defined |
| Wrong type | Cranelift panic: "type mismatch" | Use correct Cranelift type (I8 for bool, I64 for pointers) |
| Missing return | Cranelift panic: "block has no terminator" | Every block must end with a terminator |
| FFI signature mismatch | Runtime crash or wrong values | Ensure Rust function signature matches Cranelift signature exactly |
| Capture not loaded | Variable has wrong value | Load captures at outlined function entry before use |
| Generator state corruption | Wrong values after yield | Store ALL live variables, not just those explicitly used |

### Performance Tips

1. **Minimize FFI calls**: Inline simple operations, batch complex ones
2. **Use native types**: I64 for integers, F64 for floats, avoid boxing
3. **Compute offsets at compile time**: Store byte offsets in MIR, not at runtime
4. **Seal blocks early**: Call `seal_block()` as soon as all predecessors are known
5. **Clear context between functions**: Reuse `Context` and `FunctionBuilderContext`

---

## References

- `doc/status/generator_state_machine_codegen.md` - Feature 101 status
- `doc/status/future_body_execution.md` - Feature 102 status
- `doc/status/capture_buffer_vreg_remapping.md` - Feature 100 status
- `doc/status/codegen_parity_completion.md` - Feature 103 status
- `doc/feature.md` - Complete feature list with ratings
- [Cranelift Documentation](https://cranelift.dev/)
- [Cranelift IR Reference](https://github.com/bytecodealliance/wasmtime/blob/main/cranelift/docs/ir.md)
