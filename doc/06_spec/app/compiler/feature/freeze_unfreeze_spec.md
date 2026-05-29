# Freeze and Unfreeze Collections for Immutability

**Feature ID:** #LANG-025 | **Category:** Language | **Status:** Active

_Source: `test/feature/usage/freeze_unfreeze_spec.spl`_

---

## Overview

The `freeze()` function converts mutable collections (arrays and dicts) into immutable
snapshots that support read operations but prevent modification. Frozen collections
retain full access to non-mutating operations like indexing, iteration, `map`, `filter`,
`reduce`, `keys`, `values`, and `contains`. This spec validates freeze behavior on arrays
and dicts, confirms idempotence (freezing an already-frozen collection is a no-op),
and verifies that functional operations produce correct results on frozen data.

## Syntax

```simple
var arr = [1, 2, 3]
val frozen = freeze(arr)           # immutable snapshot
frozen.map(\x: x * 2)             # [2, 4, 6] - functional ops work
frozen.filter(\x: x % 2 == 0)     # filtering works on frozen

var dict = {"a": 1, "b": 2}
val frozen_dict = freeze(dict)     # frozen dict
frozen_dict.keys()                 # read-only access to keys
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| `freeze()` | Converts a mutable collection into an immutable copy |
| Idempotence | Calling `freeze()` on an already-frozen collection returns an equivalent value |
| Read-only access | Frozen collections support indexing, `len`, `first`, `last`, negative indexing |
| Functional operations | `map`, `filter`, `reduce`, `contains` all work on frozen collections |
| Dict freeze | Frozen dicts support `keys`, `values`, `contains_key`, and key-based access |

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 21 |

## Test Structure

### Freeze and Unfreeze

#### Freeze Function

- ✅ freezes mutable array
- ✅ freezes mutable dict
- ✅ is idempotent
- ✅ freezes empty array
- ✅ freezes empty dict
#### Frozen Array Operations

- ✅ allows reads on frozen array
- ✅ allows len on frozen array
- ✅ allows iteration on frozen array
- ✅ allows first and last on frozen array
- ✅ allows negative indexing on frozen array
#### Functional Operations on Frozen

- ✅ allows map on frozen array
- ✅ allows filter on frozen array
- ✅ allows reduce on frozen array
- ✅ allows contains on frozen array
#### Frozen Dict Operations

- ✅ allows reads on frozen dict
- ✅ allows len on frozen dict
- ✅ allows keys on frozen dict
- ✅ allows values on frozen dict
- ✅ allows contains_key on frozen dict
#### Type Behavior

- ✅ treats frozen arrays as arrays
- ✅ treats frozen dicts as dicts

