# hashset_basic_spec

**Category:** System/Collections | **Status:** Active

_Source: `test/feature/usage/hashset_basic_spec.spl`_

---

## Description

Integration tests for HashSet basic operations through the FFI layer.

Tests cover:
- Set creation and initialization
- Element insertion and deduplication
- Membership testing (contains/remove)
- Collection mutations (clear)
- Array conversion

**Integration Scope:** HashSet + Collections FFI
**Complexity:** Low
**Coverage Impact:** hashset.rs (0%→40%), collections FFI

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 7 |

## Test Structure

### HashSet basic operations

#### Creation and insertion

- ✅ creates new HashSet
- ✅ inserts elements
- ✅ handles duplicate insertions
#### Membership testing

- ✅ checks if element exists
- ✅ removes elements
#### Collection operations

- ✅ clears all elements
- ✅ converts to vec

