# Parser Expression Specification

Tests that the parser correctly parses various expression forms including

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-EXPR-001 to #PARSER-EXPR-030 |
| Category | Infrastructure \| Parser |
| Status | Implemented |
| Source | `test/feature/usage/parser_expressions_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 55 |
| Active scenarios | 55 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Tests that the parser correctly parses various expression forms including
arithmetic, logical, comparison, indexing, method calls, and more.

## Syntax

```simple
x + y, x - y, x * y, x / y, x % y, x ** y, x // y

x < y, x > y, x <= y, x >= y, x == y, x != y

x and y, x or y, not x

obj.method(), obj.field

arr[0], arr[i], arr[1:3]
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/parser_expressions/result.json` |

## Scenarios

- parses addition
- parses subtraction
- parses multiplication
- parses division
- parses modulo
- parses power
- parses integer division
- multiplication before addition
- parentheses override precedence
- nested parentheses
- parses unary minus
- parses bitwise not
- parses less than
- parses greater than
- parses less than or equal
- parses greater than or equal
- parses equals
- parses not equals
- parses and
- parses or
- parses not
- parses combined logical
- parses no-arg method call
- parses method call with args
- parses chained method calls
- parses field access
- parses nested field access
- parses integer index
- parses variable index
- parses expression index
- parses negative index
- parses start end slice
- parses end slice
- parses start slice
- parses no-arg call
- parses single arg call
- parses multi-arg call
- parses named arguments
- parses enum variant
- parses nested path
- parses if-else expression
- parses conditional comparison
- parses single parameter lambda
- parses multi-parameter lambda
- parses no-parameter lambda
- uses lambda with map
- parses is expression
- parses in expression
- parses not in expression
- parses deeply nested arithmetic
- parses nested collections
- parses nested method chains
- parses optional chaining
- parses null coalescing
- parses chained optional access
