# Structs Specification

Structs are user-defined data types that group related fields together. They support named fields with type annotations, default values, and can have methods defined via impl blocks. Structs are the primary way to define custom data structures in Simple.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TBD |
| Category | Language |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/feature/usage/structs_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Structs are user-defined data types that group related fields together.
They support named fields with type annotations, default values, and can
have methods defined via impl blocks. Structs are the primary way to
define custom data structures in Simple.

## Syntax

```simple
struct Point:
x: i64
y: i64

struct Config:
host: String = "localhost"
port: i64 = 8080

val p = Point { x: 3, y: 4 }
val c = Config { port: 9000 }  # host uses default
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Struct | User-defined data type with named fields |
| Field | Named member of a struct with type annotation |
| Default Value | Optional value used when field not provided |
| Construction | Creating struct instance with field values |

## Behavior

- Fields are accessed using dot notation: `point.x`
- Construction requires all fields without defaults
- Fields can have default values
- Structs are value types (copied by default)

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/structs/result.json` |

## Scenarios

- defines struct with fields
- constructs struct with all fields
- accesses struct fields
- adds method to struct
- adds method with arguments
- defines class with static method
- dispatches methods to context object
- accesses self fields in context
- calls method_missing for unknown method
- passes arguments to method_missing
