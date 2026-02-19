# LLVM Backend RISC-V 32-bit Specification

**Feature ID:** #4003 | **Category:** Infrastructure | **Difficulty:** 3/5 | **Status:** In Progress

_Source: `test/feature/usage/llvm_backend_riscv32_spec.spl`_

---

Validates that the LLVM backend correctly generates code for RISC-V 32-bit targets.

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 8 |

## Test Structure

### LLVM Backend RISC-V 32

#### target triple

- ✅ generates correct riscv32 triple
#### datalayout

- ✅ contains correct riscv32 layout
#### CPU defaults

- ✅ defaults to generic-rv32
- ✅ includes standard extensions
#### native integer type

- ✅ native_int_type is i32
#### type mapping

- ✅ uses 32-bit target_bits
#### bare-metal entry

- ✅ uses wfi instruction for halt
#### builder size type

- ✅ uses i32 size type

