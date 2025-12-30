# Feature #1: Lexer

## Overview

| Property | Value |
|----------|-------|
| **Feature ID** | #1 |
| **Feature Name** | Lexer |
| **Category** | Infrastructure |
| **Difficulty** | 3 (Medium) |
| **Status** | ✅ Complete |
| **Implementation** | Rust |

## Description

Tokenizes Simple language source code into a stream of tokens. Handles indentation-based syntax with INDENT/DEDENT tokens, string literals, numbers, identifiers, operators, and keywords.

## Specification

[doc/spec/lexer_parser.md](../../doc/spec/lexer_parser.md)

## Implementation

### Files

| File | Purpose |
|------|---------|
| `src/parser/src/lexer/mod.rs` | Implementation |
| `src/parser/src/token.rs` | Implementation |

## Testing

### Test Files

| Test File | Description |
|-----------|-------------|
| `src/parser/tests/lexer_tests.rs` | Test suite |

## Examples

```simple
# The lexer converts this:
let x = 42
if x > 0:
    print(x)
# Into tokens: LET, IDENT(x), EQ, INT(42), NEWLINE,
# IF, IDENT(x), GT, INT(0), COLON, NEWLINE, INDENT,
# IDENT(print), LPAREN, IDENT(x), RPAREN, DEDENT
```

## Dependencies

- Depends on: None (foundational component)
- Required by: #2

## Notes

First stage of compilation pipeline. Uses INDENT/DEDENT for Python-like significant whitespace.
