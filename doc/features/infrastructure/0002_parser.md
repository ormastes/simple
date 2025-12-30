# Feature #2: Parser

## Overview

| Property | Value |
|----------|-------|
| **Feature ID** | #2 |
| **Feature Name** | Parser |
| **Category** | Infrastructure |
| **Difficulty** | 4 (Hard) |
| **Status** | ✅ Complete |
| **Implementation** | Rust |

## Description

Transforms token stream into Abstract Syntax Tree (AST). Uses recursive descent for statements and Pratt parsing for expressions with operator precedence.

## Specification

[doc/spec/lexer_parser.md](../../doc/spec/lexer_parser.md)

## Implementation

### Files

| File | Purpose |
|------|---------|
| `src/parser/src/parser.rs` | Implementation |
| `src/parser/src/expressions/mod.rs` | Implementation |
| `src/parser/src/statements/mod.rs` | Implementation |

## Testing

### Test Files

| Test File | Description |
|-----------|-------------|
| `src/parser/tests/parser_tests.rs` | Test suite |

## Examples

```simple
# Parser builds AST from tokens:
fn add(a, b):
    return a + b

# AST: FnDef(name=add, params=[a,b],
#   body=[Return(BinOp(+, a, b))])
```

## Dependencies

- Depends on: #1
- Required by: #3, #4

## Notes

Pratt parser handles operator precedence elegantly. Recursive descent for control flow.
