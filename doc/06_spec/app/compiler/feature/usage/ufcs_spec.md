# UFCS (Uniform Function Call Syntax) Specification

UFCS (Uniform Function Call Syntax) allows calling free functions using method syntax. When `x.method()` is called, the compiler resolves in priority order: 1. Instance method on x's type (highest priority) 2. Trait method implemented by x's type 3. Free function `method(x)` where first param matches x's type (UFCS)

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #3100-3120 |
| Category | Syntax |
| Difficulty | 4/5 |
| Status | Implemented |
| Source | `test/feature/usage/ufcs_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

UFCS (Uniform Function Call Syntax) allows calling free functions using method syntax.
When `x.method()` is called, the compiler resolves in priority order:
1. Instance method on x's type (highest priority)
2. Trait method implemented by x's type
3. Free function `method(x)` where first param matches x's type (UFCS)

This enables fluent API chaining without requiring methods to be defined on types.

## Syntax

```simple
fn double(x: i64) -> i64:
x * 2

val n = 5
val result = n.double()    # Resolves to: double(n)
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| UFCS | Uniform Function Call Syntax - call free functions as methods |
| Resolution Priority | Instance > Trait > FreeFunction |
| Type Matching | First parameter type must be compatible with receiver |

## Implementation Notes

Files involved:
- `simple/compiler/hir.spl` - MethodResolution enum
- `simple/compiler/resolve.spl` - Resolution pass
- `simple/compiler/mir.spl` - Codegen support
- `simple/compiler/driver.spl` - Pipeline integration

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/ufcs/result.json` |

## Scenarios

- calls math.abs via dot notation
- calls math.sqrt via dot notation
- calls array.len via dot notation
- calls array.first via dot notation
- calls array.last via dot notation
- chains abs and to_string
- chains array operations
- calls string.len method not free function
- calls array.push method
- matches i64 receiver with i64 parameter
- matches f64 receiver with f64 parameter
- works with zero
- works with negative float
- len of empty array is zero
- first of empty array is None
- works with literal receiver
- works with arithmetic expression receiver
