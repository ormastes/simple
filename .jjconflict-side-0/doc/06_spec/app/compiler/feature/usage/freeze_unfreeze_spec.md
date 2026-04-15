# Freeze and Unfreeze Collections for Immutability

The `freeze()` function converts mutable collections (arrays and dicts) into immutable snapshots that support read operations but prevent modification. Frozen collections retain full access to non-mutating operations like indexing, iteration, `map`, `filter`, `reduce`, `keys`, `values`, and `contains`. This spec validates freeze behavior on arrays and dicts, confirms idempotence (freezing an already-frozen collection is a no-op), and verifies that functional operations produce correct results on frozen data.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LANG-025 |
| Category | Language |
| Status | Active |
| Source | `test/feature/usage/freeze_unfreeze_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

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

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/freeze_unfreeze/result.json` |

## Scenarios

- freezes mutable array
- freezes mutable dict
- is idempotent
- freezes empty array
- freezes empty dict
- allows reads on frozen array
- allows len on frozen array
- allows iteration on frozen array
- allows first and last on frozen array
- allows negative indexing on frozen array
- allows map on frozen array
- allows filter on frozen array
- allows reduce on frozen array
- allows contains on frozen array
- allows reads on frozen dict
- allows len on frozen dict
- allows keys on frozen dict
- allows values on frozen dict
- allows contains_key on frozen dict
- treats frozen arrays as arrays
- treats frozen dicts as dicts
