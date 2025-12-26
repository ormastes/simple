# Feature #44: Visibility Modifiers

**Status**: Implemented (Parser)
**Difficulty**: 2
**Importance**: 3

## Summary

Visibility modifiers `pub` and `priv` control access to declarations.

## Syntax

```simple
pub struct Point:
    pub x: i64
    pub y: i64
    priv _internal: i64

pub fn public_function():
    return 42

priv fn private_helper():
    return 0

pub class MyClass:
    pub value: i64
    priv secret: i64

    pub fn get_value(self):
        return self.value
```

## Features

- [x] `pub` keyword parsed
- [x] `priv` keyword parsed
- [x] `is_public` field on AST nodes:
  - FunctionDef
  - StructDef
  - ClassDef
  - EnumDef
  - TraitDef
  - TypeAliasDef
  - ExternDef
  - ConstStmt
  - StaticStmt
  - Field
- [ ] Visibility enforcement at runtime
- [ ] Module-level visibility rules

## Implementation

- **Lexer**: `TokenKind::Pub`, `TokenKind::Priv`
- **Parser**: Check for `pub`/`priv` before declarations
- **AST**: `is_public: bool` field on relevant structs

## Future Work

- Enforce visibility at module boundaries
- Private field access checking
- Protected visibility for inheritance
