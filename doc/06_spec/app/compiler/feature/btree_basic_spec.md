# btree_basic_spec

**Category:** System/Collections | **Status:** Active

_Source: `test/feature/usage/btree_basic_spec.spl`_

---

## Description

Integration tests for BTreeMap (ordered map) basic operations through the FFI layer.

Tests cover:
- Map creation and initialization
- Key-value insertion and retrieval
- Key ordering maintenance
- Key existence checking and removal
- Collection mutations (clear)
- Array/collection views (keys, values)

**Integration Scope:** BTreeMap + Collections FFI
**Complexity:** Low
**Coverage Impact:** btreemap.rs (0%→40%), collections FFI

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 7 |

## Test Structure

### BTreeMap basic operations

#### Creation and insertion

- ✅ creates new BTreeMap
- ✅ inserts and retrieves values
- ✅ maintains sorted order
#### Key operations

- ✅ checks if key exists
- ✅ removes keys
#### Collection methods

- ✅ clears all entries
- ✅ gets all values

