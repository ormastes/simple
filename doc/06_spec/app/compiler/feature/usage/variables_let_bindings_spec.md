# Variables and Bindings Specification

Tests for variable declarations including val (immutable) and var (mutable) bindings, type inference, and scoping rules.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1050 |
| Category | Language |
| Status | Implemented |
| Source | `test/feature/usage/variables_let_bindings_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Tests for variable declarations including val (immutable) and var (mutable)
bindings, type inference, and scoping rules.

## Syntax

```simple
val name = "Alice"

var count = 0
count = count + 1

var (a, b) = (1, 2)
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| val | Immutable binding - cannot be reassigned |
| var | Mutable binding - can be reassigned |

## Deprecated

- `let` - Use `val` instead
- `let mut` - Use `var` instead

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/variables_let_bindings/result.json` |

## Scenarios

- creates immutable binding
- allows shadowing with new val
- binds expression results
- binds complex expressions
- creates mutable binding
- allows multiple reassignments
- inner scope shadows outer
- inner scope can read outer
- loop variable isolated to loop
- creates immutable boolean
- creates immutable float
- initializes var with expression
- modifies var in loop
- destructures tuple into mutable bindings
- destructures tuple into immutable bindings
- infers integer type
- infers string type
- infers array type
- gets length of array
- gets length using method syntax
- binds Some value
- unwraps Some value
- binds None value
