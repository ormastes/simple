# Walrus Operator

Tests the `:=` walrus operator as syntactic sugar for `val` declarations creating immutable bindings. Covers basic bindings (integer, text, boolean, nil, float), expression evaluation, function call results, string concatenation, arrays, equivalence with val, nested scopes, control flow usage (if, loops, match), complex types (nested arrays, struct literals), and edge cases.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SYNTAX-004 |
| Category | Syntax |
| Status | Active |
| Source | `test/feature/usage/walrus_operator_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Tests the `:=` walrus operator as syntactic sugar for `val` declarations creating
immutable bindings. Covers basic bindings (integer, text, boolean, nil, float),
expression evaluation, function call results, string concatenation, arrays,
equivalence with val, nested scopes, control flow usage (if, loops, match),
complex types (nested arrays, struct literals), and edge cases.

## Syntax

```simple
x := 42
name := "Alice"
result := 10 + 32
numbers := [1, 2, 3]
```
Walrus Operator Specification

Tests the := operator as syntactic sugar for val declarations.
x := value is equivalent to val x = value (immutable binding)

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/walrus_operator/result.json` |

## Scenarios

- creates binding with integer
- creates binding with text
- creates binding with boolean
- creates binding with nil
- creates binding with float
- evaluates expression on right side
- works with function calls
- works with string concatenation
- works with arrays
- creates immutable binding
- is equivalent to val declaration
- works in nested scopes
- works in function body
- works with multiple bindings
- works with shadowing in nested scopes
- works in if branches
- works in loops
- works in match cases
- works with nested arrays
- works with struct literals
- handles parenthesized expressions
- handles chained operations
- handles boolean expressions
- walrus creates new binding
- regular assignment requires val/var
