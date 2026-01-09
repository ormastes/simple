# Feature #97: LLVM Backend

## Overview

| Property | Value |
|----------|-------|
| **Feature ID** | #97 |
| **Feature Name** | LLVM Backend |
| **Category** | Codegen |
| **Difficulty** | 5 (Very Hard) |
| **Status** | Planned |
| **Implementation** | Rust |

## Description

LLVM-based code generation backend for 32-bit architecture support and broader platform coverage. Uses same MIR and runtime FFI as Cranelift.

## Specification

[doc/codegen_technical.md](../../codegen_technical.md)

## Implementation

### Files

| File | Purpose |
|------|---------|
| (Planned) | LLVM integration |

## Architecture Support

| Architecture | Bits | Cranelift | LLVM |
|--------------|------|-----------|------|
| x86_64 | 64 | Yes | Yes |
| AArch64 | 64 | Yes | Yes |
| RISC-V 64 | 64 | Yes | Yes |
| i686 | 32 | No | Yes |
| ARMv7 | 32 | No | Yes |
| RISC-V 32 | 32 | No | Yes |

## Backend Selection

| Target | Default Backend |
|--------|-----------------|
| 64-bit | Cranelift (fast compile) |
| 32-bit | LLVM (auto-selected) |

## Testing

### Test Files

| Test File | Description |
|-----------|-------------|
| `simple/std_lib/test/features/codegen/llvm_backend_spec.spl` | BDD spec (18 tests) |

## Dependencies

- Depends on: #5
- Required by: None

## Notes

Feature-gated optional backend. Auto-selected for 32-bit targets. Supports GPU/PTX generation for CUDA.
