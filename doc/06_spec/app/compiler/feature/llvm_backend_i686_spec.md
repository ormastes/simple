# LLVM Backend i686 (x86 32-bit) Specification

**Feature ID:** #4001 | **Category:** Infrastructure | **Difficulty:** 3/5 | **Status:** In Progress

_Source: `test/feature/usage/llvm_backend_i686_spec.spl`_

---

Validates that the LLVM backend correctly generates code for 32-bit x86 (i686) targets.
This includes target triple generation, datalayout, native integer types, and CPU defaults.

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 10 |

## Test Structure

### LLVM Backend i686

#### target triple

- ✅ generates correct i686 triple
- ✅ includes correct OS in triple
#### datalayout

- ✅ contains 32-bit pointer specification
- ✅ emits datalayout in module header
#### type mapping

- ✅ uses 32-bit target_bits
#### native integer type

- ✅ native_int_type is i32
#### CPU defaults

- ✅ defaults to i686 CPU
- ✅ includes sse2 feature
#### compatibility build

- ✅ works for i686
#### builder size type

- ✅ uses i32 size type for memcpy/memset

