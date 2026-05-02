# Generic Types Specification

Tests for generic type parameters and constraints.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1005 |
| Category | Language |
| Status | In Progress |
| Source | `test/feature/usage/generics_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 28 |
| Active scenarios | 28 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Tests for generic type parameters and constraints.
Verifies generic function definitions, generic struct/class types, and type bounds.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/generics/result.json` |

## Scenarios

- defines generic identity function
- uses generic function with inference
- uses multiple type parameters
- defines generic struct
- creates instance of generic struct
- uses nested generic types
- uses tuple return type
- defines generic class
- creates generic enum
- uses generic field type
- uses list generic type
- uses where clause on function
- uses impl Trait for Type
- uses multiple trait bounds
- uses associated type
- creates generic list
- creates generic dictionary
- creates generic option
- creates generic result
- uses const generic parameter
- uses generic impl with where
- uses function type syntax
- defines function returning generic type
- uses function with generic result
- chains generic function calls
- implicitly infers type parameters
- explicitly specifies type parameters
- uses generic in method
