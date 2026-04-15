# Default Arguments Specification

Tests for function default argument values.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #DEFARG-001 |
| Category | Language \| Functions |
| Status | Implemented |
| Source | `test/feature/usage/default_arguments_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Tests for function default argument values.

## Syntax

```simple
fn greet(name, greeting="Hello"):
print "{greeting}, {name}!"

greet("Alice")           # Uses default: "Hello, Alice!"
greet("Bob", "Hi")       # Override: "Hi, Bob!"
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/default_arguments/result.json` |

## Scenarios

- uses default argument when not provided
- overrides default argument when provided
- uses multiple default arguments
- overrides some default arguments
