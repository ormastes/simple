# Default Parameter Values

Tests the `default` keyword for function parameter default values using `=` syntax. Covers basic defaults, typed parameters, methods (instance and static), collection defaults, edge cases (booleans, negatives, expressions), and combinations of required and default parameters across functions, classes, and nested scopes.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-001 |
| Category | Syntax |
| Status | Active |
| Source | `test/feature/usage/parser_default_keyword_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Tests the `default` keyword for function parameter default values using `=`
syntax. Covers basic defaults, typed parameters, methods (instance and static),
collection defaults, edge cases (booleans, negatives, expressions), and
combinations of required and default parameters across functions, classes,
and nested scopes.

## Syntax

```simple
fn greet(name = "World"):
return "Hello, {name}"
fn typed_default(count: i32 = 0):
return count
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/parser_default_keyword/result.json` |

## Scenarios

- parses default parameter value with = syntax
- parses multiple default parameters
- overrides single default parameter
- parses default with expressions
- parses default with arithmetic
- uses default in nested function
- parses default parameter with type annotation
- parses default text parameter
- parses default float parameter
- parses default in class method
- parses default in static method
- parses default empty array
- parses default array literal
- parses default with boolean
- parses default with negative number
- parses default with string interpolation
- parses mix of required and default parameters
- parses multiple functions with defaults
