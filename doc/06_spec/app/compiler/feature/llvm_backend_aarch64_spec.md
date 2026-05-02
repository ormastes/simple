# LLVM Backend AArch64 Specification

**Feature ID:** #4002 | **Category:** Infrastructure | **Difficulty:** 3/5 | **Status:** In Progress

_Source: `test/feature/usage/llvm_backend_aarch64_spec.spl`_

---

Validates that the LLVM backend correctly generates code for AArch64 (ARM 64-bit) targets.

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 10 |

## Test Structure

### LLVM Backend AArch64

#### target triple

- ✅ generates correct aarch64 triple
#### datalayout

- ✅ contains correct aarch64 layout
- ✅ emits datalayout in module header
#### CPU defaults

- ✅ defaults to cortex-a53
- ✅ includes neon feature
- ✅ includes fp-armv8 feature
#### native integer type

- ✅ native_int_type is i64
#### type mapping

- ✅ uses 64-bit target_bits
#### bare-metal entry

- ✅ uses wfi instruction for halt
#### builder size type

- ✅ uses i64 size type

