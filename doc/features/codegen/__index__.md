# Codegen Features (#95-#103)

Code generation and compilation pipeline.

## Features

| ID | Feature | Difficulty | Status | Impl |
|----|---------|------------|--------|------|
| #95 | Capture Buffer & VReg Remapping | 4 | ✅ | R |
| #96 | Generator State Machine Codegen | 5 | ✅ | R |
| #97 | LLVM Backend | 5 | ✅ | R |
| #99 | Body Block Outlining | 4 | ✅ | R |
| #100 | Cranelift Backend | 4 | ✅ | R |

## Summary

**Status:** 5/5 Complete (100%)

## Documentation

- [codegen_status.md](../codegen_status.md) - MIR instruction coverage
- `doc/llvm_backend.md` - LLVM backend details

## Test Locations

- **Rust Tests:** `src/compiler/tests/`, `src/compiler/src/codegen/llvm_tests/`
