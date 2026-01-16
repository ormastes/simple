# LLVM Backend

*Source: `simple/std_lib/test/features/codegen/llvm_backend_spec.spl`*

---

# LLVM Backend

**Feature ID:** #97
**Category:** Codegen
**Difficulty:** Level 4/5
**Status:** Complete
**Implementation:** Rust

## Overview

LLVM-based code generation backend for 32-bit architecture support and broader
platform coverage. Uses same MIR and runtime FFI as Cranelift.

## Syntax

Backend selection via compiler flags:
```bash
simple --backend=llvm script.spl     # Use LLVM backend
simple --backend=cranelift script.spl # Use Cranelift (default for 64-bit)
```

Auto-selected for 32-bit targets (i686, ARMv7, RISC-V 32).

## Implementation

**Files:**
- src/compiler/src/codegen/backend_trait.rs - Backend abstraction trait
- src/compiler/src/codegen/llvm/mod.rs - LLVM backend implementation
- src/compiler/src/codegen/llvm/types.rs - LLVM type mappings

**Tests:**
- src/compiler/src/codegen/llvm_test_utils.rs

**Dependencies:** Features #5, #100
**Required By:** None

## Notes

Feature-gated optional backend. Auto-selected for 32-bit targets. Supports GPU/PTX
generation for CUDA.
