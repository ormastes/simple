# Feature #21: String Interpolation

**Status**: Implemented
**Difficulty**: 3
**Importance**: 3

## Summary

Double-quoted strings support interpolation by default. Single-quoted strings are raw (no interpolation).

## Syntax

```simple
let name = "World"
let count = 42

# Interpolated strings (double quotes - default)
let msg = "Hello, {name}!"           # "Hello, World!"
let calc = "Count is {count + 1}"    # "Count is 43"

# Escaped braces
let code = "Use {{x}} for variables" # "Use {x} for variables"

# Raw strings (single quotes - no interpolation)
let regex = '[a-z]+\d{2,3}'          # literal backslashes and braces
let path = 'C:\Users\name'           # no escape processing
let template = '{name}'              # literal {name}, not interpolated

# Legacy f-string prefix (optional)
let old = f"Hello, {name}!"          # same as "Hello, {name}!"
```

## Features

- [x] Default interpolation in double-quoted strings
- [x] Expression evaluation in `{expr}`
- [x] Escaped braces `{{` and `}}`
- [x] Raw strings with single quotes (no escapes, no interpolation)
- [x] Legacy `f"..."` prefix support
- [x] Escape sequences in double-quoted strings (`\n`, `\t`, etc.)

## Tests

- `interpreter_fstring_basic`
- `interpreter_fstring_expression`
- `interpreter_fstring_multiple`
- `interpreter_fstring_no_interpolation`
- `interpreter_default_string_interpolation`
- `interpreter_default_string_escaped_braces`
- `interpreter_raw_string_basic`
- `interpreter_raw_string_backslashes`
- `interpreter_raw_string_no_interpolation`

## Implementation

- **Lexer**:
  - `scan_fstring()` for double-quoted strings (default)
  - `scan_raw_string()` for single-quoted strings
- **Tokens**: `FString(Vec<FStringToken>)`, `RawString(String)`
- **AST**: `Expr::FString(Vec<FStringPart>)`, `Expr::String(String)`
- **Parser**: Nested expression parsing for interpolation
