# Union Type Declarations and Discrimination

Union types allow a variable to hold a value of one of several specified types, written as `A | B`. At runtime the language provides type discrimination so that pattern matching or type-checking can narrow a union back to a concrete type. This spec is a placeholder that will be expanded once the union type feature lands; the planned coverage includes declaring union type annotations, assigning values of different member types, and narrowing via `match` with type-case arms.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LANG-034 |
| Category | Language |
| Status | Planned |
| Source | `test/feature/usage/union_types_spec.spl` |
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

Union types allow a variable to hold a value of one of several specified types,
written as `A | B`. At runtime the language provides type discrimination so that
pattern matching or type-checking can narrow a union back to a concrete type.
This spec is a placeholder that will be expanded once the union type feature
lands; the planned coverage includes declaring union type annotations, assigning
values of different member types, and narrowing via `match` with type-case arms.

## Syntax

```simple
val value: Int | Str = 42

match value:
case Int(n): print("number: {n}")
case Str(s): print("string: {s}")
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Union type (`A \| B`) | A type that can hold a value belonging to any of its member types |
| Type discrimination | Runtime mechanism to determine which member type a union value actually is |
| Pattern narrowing | Using `match` with type-case arms to safely extract the concrete value |
| Planned status | Feature is not yet implemented; spec contains a placeholder test only |

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/union_types/result.json` |

## Scenarios

- placeholder test
