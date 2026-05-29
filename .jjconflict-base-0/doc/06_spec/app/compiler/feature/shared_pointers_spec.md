# Reference Counted Pointers Specification

**Feature ID:** #SHARED-PTR | **Category:** Runtime | **Status:** Implemented

_Source: `test/feature/usage/shared_pointers_spec.spl`_

---

## Key Behaviors

- Reference count incremented on clone, decremented on drop
- Value is deallocated when reference count reaches zero
- Cloning creates shallow copy with incremented reference count

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 9 |

## Test Structure

### Reference Counted Pointers

- ✅ creates pointer
- ✅ pointer arithmetic
- ✅ multiple references
### Reference Semantics

- ✅ tracks multiple references
- ✅ clones underlying data
- ✅ dict references work correctly
### Memory Safety

- ✅ data remains valid while referenced
- ✅ strings are valid
- ✅ nested data structures work

