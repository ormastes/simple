# Single-Line Function Definitions Specification

Single-line (inline) function definitions allow functions to be defined with

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SYNTAX-INLINE |
| Category | Syntax |
| Status | Implemented |
| Source | `test/feature/usage/single_line_functions_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Single-line (inline) function definitions allow functions to be defined with
an implicit return expression on the same line as the function signature.
The syntax replaces the indented block with an expression that is automatically
returned.

## Syntax

```simple
fn name(): implicit_return_expr
fn name(param: Type) -> ReturnType: expr
```

## Key Behaviors

- Single-line functions have an implicit return expression (no explicit `return` needed)
- The expression is evaluated and returned automatically
- Explicit return types are optional but supported
- Works with zero, one, or multiple parameters
- Compatible with class methods and static functions
- Traditional block syntax is still supported and can be mixed in the same file

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/single_line_functions/result.json` |

## Scenarios

- parses inline expression body
- parses with multiple parameters
- parses with no parameters
- handles complex expressions
- returns immediately without explicit return
- supports explicit return type annotation
- works with function parameter types
- infers return type from expression
- works with class methods
- works with mutable methods
- works with static functions
- works with lambda-like expressions
- handles filtering in single line
- can coexist with traditional block functions
- block functions still work normally
- allows either style in same module
- works with nested function calls
- handles string expressions
- works with conditional expressions
