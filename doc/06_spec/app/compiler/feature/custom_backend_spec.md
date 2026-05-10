# Custom Collection Backends

**Feature ID:** #COLL-001 | **Category:** Runtime | **Status:** Active

_Source: `test/feature/usage/custom_backend_spec.spl`_

---

## Overview

Tests custom collection backend implementations including ArrayList and HashMap.
Validates that array literals can be typed as ArrayList with push/pop/get
operations, and that dictionary literals can be typed as HashMap with
key-based access and insertion.

## Syntax

```simple
val arr: ArrayList = [1, 2, 3]
arr.push(3)
val map: HashMap = {"a": 1, "b": 2}
map["b"] = 2
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 7 |

## Test Structure

### Custom Collection Backends

#### ArrayList Implementation

- ✅ should create ArrayList from array literal
- ✅ should support push
- ✅ should support pop
- ✅ should support get
#### HashMap Implementation

- ✅ should create HashMap from dict literal
- ✅ should support get
- ✅ should support insert

