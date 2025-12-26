# Feature #39: Symbols/Atoms

**Status**: Implemented
**Difficulty**: 2
**Importance**: 2

## Summary

Symbols (atoms) are lightweight, interned identifiers prefixed with `:`.

## Syntax

```simple
let status = :ok
let error = :error
let state = :pending

# Comparison
if status == :ok:
    print("Success!")

# Use in match
match result:
    :ok => handle_success()
    :error => handle_error()
```

## Features

- [x] Symbol literal syntax `:name`
- [x] Symbol comparison
- [x] Use in pattern matching
- [x] Distinct from strings

## Tests

- `interpreter_symbols`
- `interpreter_symbols_comparison`

## Implementation

- **Lexer**: `scan_symbol()` after `:` when followed by alpha
- **Token**: `TokenKind::Symbol(String)`
- **AST**: `Expr::Symbol(String)`
- **Value**: `Value::Symbol(String)`
