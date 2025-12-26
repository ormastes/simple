# Feature #43: Type Aliases

**Status**: Implemented
**Difficulty**: 2
**Importance**: 3

## Summary

Type aliases create alternative names for existing types.

## Syntax

```simple
type Number = i64
type StringList = [str]
type Handler = (i64) -> i64

fn double(x: Number) -> Number:
    return x * 2

main = double(21)  # 42
```

## Features

- [x] Basic type alias `type Name = Type`
- [x] Visibility modifier `pub type`
- [x] Use in function signatures
- [x] Alias to simple types
- [x] Alias to generic types

## Tests

- `interpreter_type_alias`

## Implementation

- **Lexer**: `TokenKind::Type` keyword
- **Parser**: `parse_type_alias()` -> `Node::TypeAlias(TypeAliasDef)`
- **AST**: `TypeAliasDef { name, ty, is_public }`
