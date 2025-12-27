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

The lexer tokenizes Simple language source code into a stream of tokens. It handles:
- Keyword recognition
- Identifier parsing
- Literal values (strings, numbers, booleans)
- Operators and punctuation
- Python-style INDENT/DEDENT tokens for block structure
- Comments (single-line `#`, multi-line `###...###`, doc `##`)

## Specification

[spec/lexer_parser.md](../../spec/lexer_parser.md)

## Implementation

### Files

| File | Purpose |
|------|---------|
| `src/parser/src/lexer/mod.rs` | Main lexer implementation |
| `src/parser/src/lexer/identifiers.rs` | Identifier and keyword handling |
| `src/parser/src/lexer/strings.rs` | String literal parsing |
| `src/parser/src/token.rs` | Token type definitions |

### Key Components

- **Tokenizer**: Converts source text to token stream
- **INDENT/DEDENT State Machine**: Tracks indentation levels for block structure
- **String Interpolation**: Handles f-string parsing with embedded expressions
- **Error Recovery**: Produces meaningful error messages with source locations

## Testing

### Rust Tests

| Test File | Description |
|-----------|-------------|
| `src/parser/tests/lexer_tests.rs` | Comprehensive lexer tests |

## Examples

```simple
# Basic tokenization
fn greet(name: str) -> str:
    return f"Hello, {name}!"

# INDENT/DEDENT handling
if condition:
    # Block start (INDENT)
    do_something()
# Block end (DEDENT)
```

## Dependencies

- Depends on: None (foundational component)
- Required by: #2 Parser, #3 AST

## Notes

- Lexer is the first stage of the compilation pipeline
- INDENT/DEDENT tokens enable Python-style whitespace-sensitive syntax
- Performance-critical: lexer speed affects overall compilation time
