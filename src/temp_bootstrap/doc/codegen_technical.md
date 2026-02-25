# Codegen Technical Documentation

This document provides detailed technical documentation for Features 99 (Body Block Outlining) and 103 (Codegen Parity Completion) in the Simple Language Compiler.

## Table of Contents

This specification is split into multiple files:

| File | Content |
|------|---------|
| [codegen_technical.md](codegen_technical.md) | Overview and Design Rationale |
| [codegen_technical_features.md](codegen_technical_features.md) | Features 99 and 103 Implementation |
| [codegen_technical_arch.md](codegen_technical_arch.md) | Architecture, FFI Interface, Testing |
| [codegen_technical_impl.md](codegen_technical_impl.md) | How to Implement (Tutorial) |

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

### Why a Multi-Stage IR (AST -> HIR -> MIR)?

**Decision**: Use three intermediate representations before codegen.

```
AST (syntax-focused) -> HIR (type-checked) -> MIR (lowered, CFG-based) -> Machine Code
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
+----------+-------------------------------------------+
| Tag (3b) |              Payload (61 bits)            |
+----------+-------------------------------------------+
```

**Rationale**:
- **Unboxed primitives**: Integers fit in payload without heap allocation
- **Fast type checks**: Single AND + compare to check type
- **Uniform representation**: All values are 64 bits, simplifies codegen

**Trade-offs**:
- 61-bit integers (not full 64-bit) for tagged representation
- Acceptable because most integers fit in 61 bits

---

## References

- `doc/status/generator_state_machine_codegen.md` - Feature 101 status
- `doc/status/future_body_execution.md` - Feature 102 status
- `doc/status/capture_buffer_vreg_remapping.md` - Feature 100 status
- `doc/status/codegen_parity_completion.md` - Feature 103 status
- `doc/feature.md` - Complete feature list with ratings
- [Cranelift Documentation](https://cranelift.dev/)
- [Cranelift IR Reference](https://github.com/bytecodealliance/wasmtime/blob/main/cranelift/docs/ir.md)

See other files for full implementation details:
- [Features 99 and 103](codegen_technical_features.md)
- [Architecture and FFI](codegen_technical_arch.md)
- [Implementation Tutorial](codegen_technical_impl.md)
