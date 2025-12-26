# Feature #19: Trailing Blocks

**Status**: Implemented
**Difficulty**: 3
**Importance**: 3

## Summary

Trailing block syntax allows passing lambdas as the last argument in a cleaner way.

## Syntax

```simple
# Instead of: items.map(\x: x * 2)
items.map \x: x * 2

# With multiple parameters
items.reduce(0) \acc, x: acc + x

# Method chains
items.filter \x: x > 0
     .map \x: x * 2
```

## Features

- [x] Trailing lambda syntax `func \params: body`
- [x] Works with function calls
- [x] Works with method calls
- [x] Multiple parameters in trailing block
- [x] Can combine with regular arguments

## Tests

- `interpreter_trailing_block_with_args`
- `interpreter_trailing_block_filter`
- `interpreter_trailing_block_multi_param`
- `interpreter_trailing_block_method_call`

## Implementation

- **Parser**: `parse_trailing_lambda()` after call detection
- **Lexer**: `TokenKind::Backslash` triggers trailing block
- **AST**: Appended as last `Argument` in call
