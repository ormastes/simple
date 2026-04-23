# Parser Function Definition Specification

Tests that the parser correctly parses function definitions including

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-FN-001 to #PARSER-FN-020 |
| Category | Infrastructure \| Parser |
| Status | Implemented |
| Source | `test/feature/usage/parser_functions_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Tests that the parser correctly parses function definitions including
parameters, return types, generics, where clauses, and various function forms.

## Syntax

```simple
fn name(params) -> ReturnType:
body

fn generic<T>(x: T) -> T where T: Trait:
body

extern fn ffi_func(x: i64) -> i64

macro name(params) -> (contract):
body
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/parser_functions/result.json` |

## Scenarios

- parses function without params
- parses function with single param
- parses function with multiple params
- parses explicit return type
- parses inferred return
- parses unit return
- parses multi-statement body
- parses recursive function
- parses single type parameter
- parses multiple type parameters
- parses nested generic types
- parses single where clause
- parses multiple bounds
- parses multiple where clauses
- parses default parameter
- parses multiple defaults
- parses mixed required and default
- parses named arguments
- parses mixed positional and named
- parses named arguments in any order
- parses extern function
- parses extern with multiple params
- parses macro definition
- parses actor definition
- parses method with self
- parses mutable method
- parses static method
- parses simple lambda
- parses multi-param lambda
- parses typed lambda
- parses lambda in higher-order context
- parses async function
- parses await expression
