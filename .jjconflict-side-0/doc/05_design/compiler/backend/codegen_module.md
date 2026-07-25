# Codegen Module Design

This document describes the architecture of the codegen module, which handles compilation of MIR (Mid-level IR) to native machine code using Cranelift.

## Module Overview

The codegen module provides two compilation backends:
- **AOT (Ahead-of-Time)**: Compiles to object files for static linking
- **JIT (Just-in-Time)**: Compiles to executable memory for runtime execution

Both backends share significant infrastructure through the `shared`, `runtime_ffi`, and `types_util` modules.

## Architecture Diagram

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                           Codegen Module                                     │
│                    src/compiler/src/codegen/                                │
└─────────────────────────────────────────────────────────────────────────────┘
                                    │
         ┌──────────────────────────┼──────────────────────────┐
         │                          │                          │
         ▼                          ▼                          ▼
┌─────────────────┐      ┌─────────────────┐      ┌─────────────────────────┐
│   AOT Backend   │      │   JIT Backend   │      │    Shared Infrastructure │
│  cranelift.rs   │      │     jit.rs      │      │                          │
│    (461 loc)    │      │    (521 loc)    │      │  ┌───────────────────┐  │
└────────┬────────┘      └────────┬────────┘      │  │    shared.rs      │  │
         │                        │               │  │    (212 loc)      │  │
         │                        │               │  │  ─────────────────│  │
         │                        │               │  │ • build_mir_sig   │  │
         │                        │               │  │ • expand_outlined │  │
         │                        │               │  │ • get_func_addr   │  │
         │                        │               │  │ • create_outlined │  │
         │                        │               │  └───────────────────┘  │
         │                        │               │                          │
         │                        │               │  ┌───────────────────┐  │
         │                        │               │  │  runtime_ffi.rs   │  │
         │                        │               │  │    (177 loc)      │  │
         │                        │               │  │  ─────────────────│  │
         │                        │               │  │ • RuntimeFuncSpec │  │
         │                        │               │  │ • RUNTIME_FUNCS   │  │
         │                        │               │  │   (50+ FFI specs) │  │
         │                        │               │  └───────────────────┘  │
         │                        │               │                          │
         │                        │               │  ┌───────────────────┐  │
         │                        │               │  │   types_util.rs   │  │
         │                        │               │  │     (93 loc)      │  │
         │                        │               │  │  ─────────────────│  │
         │                        │               │  │ • type_id_to_cl   │  │
         │                        │               │  │ • type_id_size    │  │
         │                        │               │  │ • type_to_cl      │  │
         │                        │               │  └───────────────────┘  │
         │                        │               └─────────────────────────┘
         │                        │
         ▼                        ▼
┌─────────────────┐      ┌─────────────────┐
│cranelift_instr  │      │   jit_instr.rs  │
│     .rs         │      │    (1741 loc)   │
│  (1800 loc)     │      │                 │
│                 │      │  MIR instruction│
│ MIR instruction │      │  -> Cranelift   │
│ -> Cranelift    │      │  IR translation │
│ IR translation  │      │                 │
└────────┬────────┘      └────────┬────────┘
         │                        │
         │     include!()         │     include!()
         │     macro              │     macro
         └────────┬───────────────┘
                  │
                  ▼
         ┌────────────────┐
         │  50+ MIR Instr │
         │   Handlers     │
         │  ─────────────│
         │ • ConstInt     │
         │ • BinOp        │
         │ • ArrayLit     │
         │ • ClosureCall  │
         │ • ActorSpawn   │
         │ • Yield        │
         │ • ...          │
         └────────────────┘
```

## File Structure

```
src/compiler/src/codegen/
├── mod.rs              (8 loc)    # Module exports
├── shared.rs           (212 loc)  # Shared utilities for AOT/JIT
├── runtime_ffi.rs      (177 loc)  # FFI function specifications
├── types_util.rs       (93 loc)   # Type conversion utilities
├── cranelift.rs        (461 loc)  # AOT backend entry point
├── cranelift_instr.rs  (1800 loc) # AOT instruction compilation
├── cranelift_tests.rs  (40 loc)   # AOT tests
├── jit.rs              (521 loc)  # JIT backend entry point
├── jit_instr.rs        (1741 loc) # JIT instruction compilation
└── jit_tests.rs        (81 loc)   # JIT tests
                        ──────────
                Total:  5134 loc
```

## Module Responsibilities

### 1. shared.rs - Shared Utilities

Extracted common functionality used by both AOT and JIT backends:

| Function | Description |
|----------|-------------|
| `build_mir_signature()` | Builds Cranelift function signature from MIR function |
| `expand_with_outlined()` | Expands MIR module with outlined functions for actors/generators/futures |
| `get_func_block_addr()` | Gets function address for outlined block (generic over Module type) |
| `create_outlined_function()` | Creates outlined function from parent's body block |
| `get_body_kind()` | Extracts body kind (Actor/Generator/Future) from MIR instruction |

```rust
// Generic function that works with both ObjectModule (AOT) and JITModule
pub fn get_func_block_addr<M: Module>(
    func_ids: &HashMap<String, FuncId>,
    module: &mut M,
    parent_name: &str,
    block: BlockId,
    builder: &mut FunctionBuilder,
) -> cranelift_codegen::ir::Value
```

### 2. runtime_ffi.rs - Runtime FFI Specifications

Defines all runtime function signatures that codegen needs to call:

| Category | Functions | Description |
|----------|-----------|-------------|
| Array | 6 | `rt_array_new`, `_push`, `_get`, `_set`, `_pop`, `_clear` |
| Tuple | 4 | `rt_tuple_new`, `_set`, `_get`, `_len` |
| Dict | 7 | `rt_dict_new`, `_set`, `_get`, `_len`, `_clear`, `_keys`, `_values` |
| Index/Slice | 4 | `rt_index_get`, `_set`, `rt_slice`, `rt_contains` |
| String | 2 | `rt_string_new`, `_concat` |
| Value | 4 | `rt_value_int`, `_float`, `_bool`, `_nil` |
| Object | 3 | `rt_object_new`, `_field_get`, `_field_set` |
| Closure | 4 | `rt_closure_new`, `_set_capture`, `_get_capture`, `_func_ptr` |
| Enum | 3 | `rt_enum_new`, `_discriminant`, `_payload` |
| Memory | 4 | `rt_alloc`, `_free`, `_ptr_to_value`, `_value_to_ptr` |
| Async | 6 | `rt_wait`, `rt_future_*`, `rt_actor_*` |
| Generator | 8 | `rt_generator_*` |
| Interp Bridge | 2 | `rt_interp_call`, `rt_interp_eval` |
| Error | 2 | `rt_function_not_found`, `rt_method_not_found` |

### 3. types_util.rs - Type Conversion

Maps Simple language types to Cranelift IR types:

```rust
pub fn type_to_cranelift(ty: TypeId) -> types::Type {
    match ty {
        TypeId::BOOL => types::I8,
        TypeId::I8 | TypeId::U8 => types::I8,
        TypeId::I16 | TypeId::U16 => types::I16,
        TypeId::I32 | TypeId::U32 => types::I32,
        TypeId::I64 | TypeId::U64 => types::I64,
        TypeId::F32 => types::F32,
        TypeId::F64 => types::F64,
        _ => types::I64,  // Pointers, RuntimeValue
    }
}
```

### 4. cranelift.rs / jit.rs - Backend Entry Points

| Aspect | AOT (cranelift.rs) | JIT (jit.rs) |
|--------|-------------------|--------------|
| Module Type | `ObjectModule` | `JITModule` |
| Error Type | `CodegenError` | `JitError` |
| Output | `Vec<u8>` (object code) | In-memory function pointers |
| Settings | `opt_level=speed` | `opt_level=speed, is_pic=true` |
| Finalization | `module.finish().emit()` | `module.finalize_definitions()` |

Shared operations (now in shared.rs):
- Function signature building
- Outlined function expansion
- Variable/block creation
- Generator state machine dispatch

### 5. cranelift_instr.rs / jit_instr.rs - Instruction Compilation

Both files handle 50+ MIR instruction types. They are included via `include!()` macro into the main compilation loop:

```rust
// In cranelift.rs compile_function()
for inst in &mir_block.instructions {
    include!("cranelift_instr.rs");
}
```

Instruction categories:
- **Core**: ConstInt, ConstFloat, BinOp, UnaryOp, Copy, Phi
- **Memory**: Load, Store, GcAlloc, LocalAddr, Wait
- **Collections**: ArrayLit, TupleLit, DictLit, IndexGet, IndexSet, Slice
- **Strings**: ConstString, ConstSymbol, FStringFormat
- **Closures**: ClosureCreate, ClosureCapture, IndirectCall
- **Objects**: StructInit, FieldGet, FieldSet, MethodCall, VTableLookup
- **Patterns**: PatternTest, PatternBind, EnumDiscriminant, EnumPayload
- **Async**: FutureCreate, Await, ActorSpawn, ActorSend, ActorRecv
- **Generators**: GeneratorCreate, Yield, GeneratorNext
- **Errors**: TryUnwrap, OptionSome, OptionNone, ResultOk, ResultErr
- **Fallback**: InterpCall, InterpEval (interpreter bridge)

## Data Flow

```
┌─────────────┐     ┌─────────────┐     ┌─────────────────┐
│  MirModule  │────▶│expand_with_ │────▶│ Vec<MirFunction>│
│             │     │  outlined() │     │ (+ outlined fns)│
└─────────────┘     └─────────────┘     └────────┬────────┘
                                                  │
                    ┌─────────────────────────────┘
                    │
                    ▼
         ┌──────────────────┐
         │ For each function│
         └────────┬─────────┘
                  │
    ┌─────────────┼─────────────┐
    │             │             │
    ▼             ▼             ▼
┌────────┐   ┌────────┐   ┌────────┐
│Declare │   │ Build  │   │Compile │
│Function│──▶│  Sig   │──▶│  Body  │
└────────┘   └────────┘   └────────┘
                              │
              ┌───────────────┼───────────────┐
              │               │               │
              ▼               ▼               ▼
        ┌──────────┐   ┌──────────┐   ┌──────────┐
        │Variables │   │  Blocks  │   │Generator │
        │& Params  │   │& Jumps   │   │State Mach│
        └──────────┘   └──────────┘   └──────────┘
              │               │               │
              └───────────────┼───────────────┘
                              │
                              ▼
                    ┌─────────────────┐
                    │ For each block  │
                    └────────┬────────┘
                             │
                             ▼
                    ┌─────────────────┐
                    │  Instructions   │
                    │  (include!())   │
                    └────────┬────────┘
                             │
                             ▼
                    ┌─────────────────┐
                    │   Terminator    │
                    │ Return/Jump/Br  │
                    └────────┬────────┘
                             │
              ┌──────────────┴──────────────┐
              │                             │
              ▼                             ▼
      ┌─────────────┐               ┌─────────────┐
      │  AOT: emit  │               │ JIT: get_   │
      │ object code │               │function_ptr │
      └─────────────┘               └─────────────┘
```

## Duplication Analysis

### Before Refactoring
- `expand_with_outlined()`: ~120 lines duplicated in both backends
- `build_signature()`: ~15 lines duplicated
- `func_block_addr()`: ~10 lines duplicated
- **Total duplicated**: ~145+ lines

### After Refactoring
- Extracted to `shared.rs`: 212 lines (with additional helpers)
- Remaining unique in AOT: `ensure_body_stub()`, AOT-specific error handling
- Remaining unique in JIT: `ensure_body_stub()`, function pointer management, `call_*` methods

### Current Duplication (jscpd report)
The `cranelift_instr.rs` and `jit_instr.rs` files still have significant structural similarity (~1800 vs ~1741 lines). This is intentional because:
1. They handle the same 50+ instruction types
2. Minor differences in error types and module types
3. Future optimization: could potentially be unified with generics

## Extension Points

### Adding New MIR Instructions
1. Add instruction handler in both `cranelift_instr.rs` and `jit_instr.rs`
2. If instruction needs runtime support, add to `RUNTIME_FUNCS` in `runtime_ffi.rs`
3. Implement corresponding runtime function in `src/runtime/src/value/`

### Adding New Runtime Functions
1. Add `RuntimeFuncSpec` entry to `RUNTIME_FUNCS` array
2. Implement function in runtime module with matching signature
3. Use via `self.runtime_funcs["rt_func_name"]` in instruction compilation

### Adding New Type Support
1. Update `type_id_to_cranelift()` and `type_to_cranelift()` in `types_util.rs`
2. Update `type_id_size()` if needed for memory layout

## Testing Strategy

| Test File | Coverage |
|-----------|----------|
| `cranelift_tests.rs` | AOT compilation paths |
| `jit_tests.rs` | JIT compilation and execution |
| `runtime_ffi.rs` (tests) | FFI spec validation |
| `types_util.rs` (tests) | Type conversion correctness |
| Integration tests | End-to-end compilation + execution |

## Performance Considerations

1. **Shared code** reduces maintenance burden but doesn't affect runtime performance
2. **Instruction compilation** is the main cost - `include!()` has no runtime overhead
3. **Function outlining** for generators/actors adds one-time compilation cost
4. **JIT** has additional `finalize_definitions()` overhead for memory protection changes
