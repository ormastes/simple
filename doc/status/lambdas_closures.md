# Feature #17: Lambdas/Closures

**Status**: Implemented
**Difficulty**: 4
**Importance**: 4

## Summary

Lambda expressions with closure capture are fully implemented.

## Syntax

```simple
# Basic lambda
let double = \x: x * 2

# Multiple parameters
let add = \x, y: x + y

# No parameters
let get_value = \: 42

# Immediate call
let result = (\x: x + 1)(5)
```

## Features

- [x] Basic lambda syntax `\params: body`
- [x] Multiple parameters `\x, y: expr`
- [x] No-parameter lambdas `\: expr`
- [x] Closure capture (captured environment)
- [x] Nested lambdas
- [x] Immediate invocation
- [x] Use with higher-order functions (map, filter, reduce)

## Tests

- `interpreter_lambda_simple`
- `interpreter_lambda_multiple_params`
- `interpreter_lambda_closure`
- `interpreter_lambda_immediate_call`
- `interpreter_lambda_nested`
- `interpreter_lambda_no_params`

## Implementation

- **Parser**: `parse_trailing_lambda()` in `parser.rs`
- **AST**: `Expr::Lambda { params, body }` and `LambdaParam` in `ast.rs`
- **Interpreter**: `Value::Lambda { params, body, env }` with captured environment
- **Execution**: `exec_lambda()` function handles lambda calls
