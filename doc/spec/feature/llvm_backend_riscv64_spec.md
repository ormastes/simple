# LLVM Backend RISC-V 64-bit Specification

**Feature ID:** #4005 | **Category:** Infrastructure | **Difficulty:** 3/5 | **Status:** In Progress

_Source: `test/feature/usage/llvm_backend_riscv64_spec.spl`_

---

Validates that the LLVM backend correctly generates code for RISC-V 64-bit targets.

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 8 |

## Test Structure

### LLVM Backend RISC-V 64

#### target triple

- ✅ generates correct riscv64 triple
#### datalayout

- ✅ contains correct riscv64 layout
#### CPU defaults

- ✅ defaults to generic-rv64
- ✅ includes standard extensions
#### native integer type

- ✅ native_int_type is i64
#### type mapping

- ✅ uses 64-bit target_bits
#### bare-metal entry

- ✅ uses wfi instruction for halt
#### builder size type

- ✅ uses i64 size type

