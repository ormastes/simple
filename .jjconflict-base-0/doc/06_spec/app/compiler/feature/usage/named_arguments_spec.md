# Named Arguments Specification

Tests for named argument support allowing function calls with explicit parameter names, improving code clarity and enabling flexible argument ordering.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #NAMED-ARGS-001 |
| Category | Language \| Functions |
| Status | Implemented |
| Source | `test/feature/usage/named_arguments_spec.spl` |
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

Tests for named argument support allowing function calls with explicit
parameter names, improving code clarity and enabling flexible argument ordering.

## Syntax

```simple
fn create_user(name: text, email: text, age: i64) -> User:
User(name: name, email: email, age: age)

val user1 = create_user("Alice", "alice@example.com", 30)

val user2 = create_user(age=25, name="Bob", email="bob@example.com")

val user3 = create_user("Charlie", email="charlie@example.com", age=35)
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Named Argument | Explicitly passing parameter by name |
| Positional Argument | Passing argument by position order |
| Argument Reordering | Non-positional order with named arguments |
| Default Values | Optional parameters with defaults |
| Clarity | Improved code readability with explicit parameter names |

## Behavior

- Named arguments can be passed in any order
- Positional arguments must precede named arguments (if mixed)
- Parameter names are part of the function signature
- Type checking applies to named arguments like positional
- Named arguments cannot be repeated in a single call
- Works with constructors and regular functions

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/named_arguments/result.json` |

## Scenarios

- calls function with named arguments
- passes values correctly with named arguments
- works with string values
- allows reversed argument order
- reorders three arguments
- reorders with different calculation
- mixes positional and named arguments
- uses positional first then named
- uses single positional with multiple named
- uses default when argument not provided
- overrides default with named argument
- works with multiple defaults
- uses named arguments with class methods
- reorders method arguments
- handles single named argument
- handles many named arguments
- works with nested function calls
