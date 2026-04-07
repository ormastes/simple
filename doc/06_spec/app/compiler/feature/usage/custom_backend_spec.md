# Custom Collection Backends

Tests custom collection backend implementations including ArrayList and HashMap. Validates that array literals can be typed as ArrayList with push/pop/get operations, and that dictionary literals can be typed as HashMap with key-based access and insertion.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #COLL-001 |
| Category | Runtime |
| Status | Active |
| Source | `test/feature/usage/custom_backend_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

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
Custom Collection Backends - SSpec Tests

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/custom_backend/result.json` |

## Scenarios

- should create ArrayList from array literal
- should support push
- should support pop
- should support get
- should create HashMap from dict literal
- should support get
- should support insert
