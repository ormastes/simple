# LLVM Backend Codegen Specification

The LLVM backend provides high-performance native code generation for the Simple language

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #4000 |
| Category | Infrastructure |
| Difficulty | 5/5 |
| Status | In Progress |
| Source | `test/feature/usage/llvm_backend_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 32 |
| Active scenarios | 32 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

The LLVM backend provides high-performance native code generation for the Simple language
compiler. It converts the compiler's Intermediate Representation (MIR) to LLVM IR, enabling
optimized machine code generation for multiple target platforms. This specification covers
LLVM IR generation, optimization passes, linking, and target-specific code generation.

## Key Concepts

| Concept | Description |
|---------|-------------|
| LLVM IR | Intermediate representation compatible with LLVM compiler framework |
| MIR to LLVM | Conversion pipeline from Simple's MIR to LLVM IR |
| Optimization Passes | LLVM-level optimizations (inlining, dead code elimination, etc) |
| Code Generation | Conversion of LLVM IR to native machine code |
| Target Platform | Architecture and OS-specific code generation (x86_64, ARM, etc) |
| Linking | Integration with system linker and native libraries |

## Behavior

The LLVM backend:
- Translates MIR instructions to equivalent LLVM IR constructs
- Preserves type information and memory semantics
- Enables high-level optimizations through LLVM optimization passes
- Generates platform-specific machine code
- Integrates with native linkers for final executable generation
- Supports multiple target architectures and operating systems

## Implementation Notes

- LLVM IR generation uses the `inkwell` Rust bindings
- Optimization level controlled via compiler flags
- Target triple determines platform-specific behavior
- Function attributes affect code generation and optimization
- Debug information preserved for debugging support

## Related Specifications

- Intermediate Representation (MIR format specification)
- Memory Model (reference capabilities and ownership rules)
- FFI Integration (native function calling conventions)
- Type System (type information preservation in codegen)

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/llvm_backend/result.json` |

## Scenarios

- generates code for integer addition
- generates code for integer multiplication
- generates code for floating-point operations
- generates code for if-else branches
- generates code for loops
- handles function calls
- handles recursive function calls
- generates code for variable assignment
- handles mutable struct fields
- generates code for list operations
- generates code for map operations
- generates code for type conversions
- preserves correct semantics under optimization
- maintains correct results with loop optimization
- generates passes for optimization levels
- emits debug info header
- emits typed function calls
- emits datalayout for x86_64
- emits datalayout for i686
- emits datalayout for aarch64
- emits datalayout before target triple
- native_int_type is i32 for 32-bit targets
- native_int_type is i64 for 64-bit targets
- type mapper uses 32-bit pointers for i686
- type mapper uses 64-bit pointers for x86_64
- builder size_type is i32 for 32-bit targets
- builder size_type is i64 for 64-bit targets
- selects correct CPU for x86_64
- selects correct CPU for i686
- selects correct CPU for aarch64
- selects correct CPU for riscv64
- selects correct CPU for riscv32
