# Primitive Types Specification

Tests for primitive types, type suffixes, union types, type aliases, and generic types.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PRIM-001 |
| Category | Language \| Types |
| Status | Implemented |
| Source | `test/feature/usage/primitive_types_spec.spl` |
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

Tests for primitive types, type suffixes, union types, type aliases,
and generic types.

## Syntax

```simple
val x = 42i32                             # Type suffix
type Number = i64                         # Type alias
fn process(x: i64 | str) -> i64: ...      # Union type
fn identity<T>(x: T) -> T: x              # Generic function
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/primitive_types/result.json` |

## Scenarios

- compares enum variants
- accepts union type parameter
- uses simple type alias
- accepts optional parameter
- defines identity function
- uses two type parameters
- creates generic struct
- unwraps Some value
- unwraps None with default
- checks is_some
- checks is_none
- maps Some value
- uses i32 suffix
- uses i64 suffix
- uses u32 suffix
- uses unit suffix km
- uses unit suffix in expression
- uses f64 suffix
- uses f32 suffix
- matches exhaustively without wildcard
- allows wildcard in weak enum
