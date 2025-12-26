# Feature #46: Extern Functions (FFI)

**Status**: Implemented
**Difficulty**: 4
**Importance**: 3

## Summary

Extern functions declare external (built-in) functions callable from Simple code.

## Syntax

```simple
extern fn abs(x: i64) -> i64
extern fn sqrt(x: f64) -> f64
extern fn pow(base: f64, exp: f64) -> f64
extern fn min(a: i64, b: i64) -> i64
extern fn max(a: i64, b: i64) -> i64
extern fn to_int(x: f64) -> i64

# Usage
let x = abs(-42)      # 42
let y = sqrt(16.0)    # 4.0
let z = pow(2.0, 3.0) # 8.0
```

## Built-in Extern Functions

- `abs(x)` - Absolute value
- `sqrt(x)` - Square root
- `pow(base, exp)` - Exponentiation
- `min(a, b)` - Minimum
- `max(a, b)` - Maximum
- `to_int(x)` - Float to integer conversion

## Features

- [x] `extern fn` declaration syntax
- [x] Parameter types
- [x] Return type
- [x] Visibility modifier support
- [x] Built-in function implementations

## Tests

- `interpreter_extern_abs`
- `interpreter_extern_sqrt`
- `interpreter_extern_pow`
- `interpreter_extern_min_max`
- `interpreter_extern_to_int`

## Implementation

- **Lexer**: `TokenKind::Extern` keyword
- **Parser**: `parse_extern()` -> `Node::Extern(ExternDef)`
- **AST**: `ExternDef { name, params, return_type, is_public }`
- **Interpreter**: `EXTERN_FUNCTIONS` thread-local registry, `call_extern_function()`
