# Codegen Features 99 and 103

Part of [Codegen Technical Documentation](codegen_technical.md).

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

---

Next: [Architecture and FFI](codegen_technical_arch.md)
