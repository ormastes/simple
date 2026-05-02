# LLVM Backend ARM 32-bit Specification

**Feature ID:** #4004 | **Category:** Infrastructure | **Difficulty:** 3/5 | **Status:** In Progress

_Source: `test/feature/usage/llvm_backend_arm32_spec.spl`_

---

Validates that the LLVM backend correctly generates code for ARM 32-bit (ARMv7) targets.

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 10 |

## Test Structure

### LLVM Backend ARM32

#### target triple

- ✅ generates correct armv7 triple
- ✅ includes gnueabihf env on linux
#### datalayout

- ✅ contains correct arm32 layout
#### CPU defaults

- ✅ defaults to cortex-a7
- ✅ includes neon feature
- ✅ includes vfp4 feature
#### native integer type

- ✅ native_int_type is i32
#### type mapping

- ✅ uses 32-bit target_bits
#### bare-metal entry

- ✅ uses wfi instruction for halt
#### builder size type

- ✅ uses i32 size type

