# Codegen Features (#95-#97, #100-#101)

Code generation and compilation backends.

## Features

| ID | Feature | Difficulty | Status | Impl |
|----|---------|------------|--------|------|
| #95 | [Buffer Pool](0095_buffer_pool.md) | 3 | Complete | Rust |
| #96 | [Generator Codegen](0096_generator_codegen.md) | 4 | Complete | Rust |
| #97 | [LLVM Backend](0097_llvm_backend.md) | 5 | Planned | Rust |
| #100 | [Cranelift Backend](0100_cranelift_backend.md) | 4 | Complete | Rust |
| #101 | [Native Binary](0101_native_binary.md) | 4 | In Progress | Rust |

## Summary

**Status:** 3/5 Complete (60%)

## Test Locations

- **Simple Tests:** `simple/std_lib/test/features/codegen/`
- **Rust Tests:** `src/driver/tests/interpreter_jit_tests.rs`

## Backend Status

| Backend | AOT | JIT | Status |
|---------|-----|-----|--------|
| Cranelift | Yes | Yes | Primary |
| LLVM | Planned | No | Alternative |
| Interpreter | N/A | Yes | Fallback |

## Native Binary Pipeline

```
MIR -> Cranelift -> Object Files -> Linker (mold/lld) -> Native Binary
```
