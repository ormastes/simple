# Feature #35: Context Blocks

**Status**: Implemented
**Difficulty**: 3
**Importance**: 2

## Summary

Context blocks provide DSL-like syntax where method calls are implicitly dispatched to a context object.

## Syntax

```simple
class Builder:
    value: i64 = 0

    fn set(self, x):
        self.value = x
        return self

    fn add(self, x):
        self.value = self.value + x
        return self

let b = Builder { value: 0 }
context b:
    set(10)      # Calls b.set(10)
    add(5)       # Calls b.add(5)
    add(3)       # Calls b.add(3)

# b.value is now 18
```

## Features

- [x] `context expr:` block syntax
- [x] Implicit method dispatch to context object
- [x] Access to `self` in methods
- [x] Nested context blocks
- [x] Integration with method_missing

## Tests

- `interpreter_context_block_basic`
- `interpreter_context_block_with_self`
- `interpreter_method_missing_with_context`

## Implementation

- **Lexer**: `TokenKind::Context` keyword
- **Parser**: `parse_context()` -> `Node::Context(ContextStmt)`
- **AST**: `ContextStmt { context: Expr, body: Block }`
- **Interpreter**: Thread-local `CONTEXT_OBJECT` for dispatch
