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

The parser transforms the token stream from the lexer into an Abstract Syntax Tree (AST). It implements:
- Recursive descent parsing for statements
- Pratt parser for expressions (precedence climbing)
- Error recovery for better diagnostics
- Modular architecture (expressions, statements, types)

## Specification

[spec/lexer_parser.md](../../spec/lexer_parser.md)

## Implementation

### Files

| File | Purpose |
|------|---------|
| `src/parser/src/parser_impl/core.rs` | Main parser implementation |
| `src/parser/src/parser_impl/items.rs` | Top-level item parsing |
| `src/parser/src/expressions/mod.rs` | Expression parsing (Pratt parser) |
| `src/parser/src/statements/mod.rs` | Statement parsing |
| `src/parser/src/types_def/mod.rs` | Type annotation parsing |

### Key Components

- **Recursive Descent**: Top-down parsing for statements and declarations
- **Pratt Parser**: Precedence climbing for expressions
- **Error Recovery**: Synchronization at statement boundaries
- **Span Tracking**: Source location for all AST nodes

## Testing

### Rust Tests

| Test File | Description |
|-----------|-------------|
| `src/parser/tests/expression_tests.rs` | Expression parsing tests |
| `src/parser/tests/statement_tests.rs` | Statement parsing tests |
| `src/parser/tests/type_tests.rs` | Type parsing tests |
| `src/parser/tests/error_tests.rs` | Error recovery tests |

## Examples

```simple
# Parsed into function definition AST node
fn factorial(n: i64) -> i64:
    if n <= 1:
        return 1
    return n * factorial(n - 1)

# Expression parsing with precedence
let result = a + b * c  # Parsed as: a + (b * c)
```

## Dependencies

- Depends on: #1 Lexer
- Required by: #4 HIR, all language features

## Notes

- Parser is the second stage of the compilation pipeline
- Modular design allows easy extension for new language features
- Error messages include source context for debugging
