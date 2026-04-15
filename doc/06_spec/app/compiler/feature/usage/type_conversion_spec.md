# Automatic Type Annotation Conversion

Type annotation conversion allows a value to be automatically converted to a specified target type when the annotation differs from the literal form. For example, declaring `val arr: ArrayList = [1, 2, 3]` would implicitly convert the array literal into an `ArrayList` instance. This feature is currently deferred, so the spec validates the baseline behavior: arrays work correctly without explicit type conversion annotations, ensuring that the standard array literal syntax remains functional as the foundation for future auto-conversion support.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LANG-007 |
| Category | Language |
| Status | In Progress |
| Source | `test/feature/usage/type_conversion_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Type annotation conversion allows a value to be automatically converted to a specified
target type when the annotation differs from the literal form. For example, declaring
`val arr: ArrayList = [1, 2, 3]` would implicitly convert the array literal into an
`ArrayList` instance. This feature is currently deferred, so the spec validates the
baseline behavior: arrays work correctly without explicit type conversion annotations,
ensuring that the standard array literal syntax remains functional as the foundation
for future auto-conversion support.

## Syntax

```simple
val arr = [1, 2, 3]
expect arr[0] == 1
expect arr.len() == 3
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Type Annotation | A declared type on a binding, e.g., `val x: SomeType = value` |
| Auto-Conversion | Planned implicit conversion of a literal to match its declared type |
| Array Literal | The `[1, 2, 3]` syntax that creates a default array without annotation |
| Deferred Status | Feature is designed but not yet implemented; spec guards baseline behavior |

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/type_conversion/result.json` |

## Scenarios

- arrays work without type conversion
