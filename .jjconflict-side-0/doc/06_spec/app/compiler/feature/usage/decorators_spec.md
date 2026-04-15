# Decorators Specification

Decorators are functions that transform other functions, enabling aspect-oriented programming patterns like logging, caching, and validation.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #DECO-001 |
| Category | Language \| Functions |
| Status | Implemented |
| Source | `test/feature/usage/decorators_spec.spl` |
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

Decorators are functions that transform other functions, enabling
aspect-oriented programming patterns like logging, caching, and validation.

## Syntax

```simple
@double_result
fn add_one(x):
return x + 1

@multiply_by(3)
fn increment(x):
return x + 1
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/decorators/result.json` |

## Scenarios

- applies basic decorator
- applies decorator with arguments
- stacks multiple decorators
- uses decorator without parentheses
- uses inline attribute
- uses deprecated attribute
- uses deprecated with message
- stacks multiple attributes
- executes basic with block
- binds value with as clause
