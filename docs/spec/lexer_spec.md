# Lexer

*Source: `simple/std_lib/test/features/infrastructure/lexer_spec.spl`*

---

# Lexer

**Feature ID:** #1
**Category:** Infrastructure
**Difficulty:** 3/5
**Status:** Complete

## Overview

Tokenizes Simple language source code into a stream of tokens. Handles indentation-based syntax with INDENT/DEDENT tokens, string literals, numbers, identifiers, operators, and keywords.

## Syntax

The lexer tokenizes:
```simple
val x = 42
if x > 0:
    print(x)
```

Into tokens: `LET`, `IDENT(x)`, `EQ`, `INT(42)`, `NEWLINE`, `IF`, `IDENT(x)`, `GT`, `INT(0)`, `COLON`, `NEWLINE`, `INDENT`, `IDENT(print)`, `LPAREN`, `IDENT(x)`, `RPAREN`, `DEDENT`

**Token Categories:**
- Literals: integers, floats, strings, f-strings
- Identifiers: variable and function names
- Operators: arithmetic (+, -, *, /), comparison (>, <, ==), logical (and, or, not)
- Keywords: val, var, fn, if, match, etc.
- Indentation: INDENT/DEDENT for block structure

## Implementation

**Files:**
- `src/parser/src/lexer/mod.rs`
- `src/parser/src/token.rs`

**Test Files:**
- `src/parser/tests/lexer_tests.rs`

**Dependencies:** (none)
**Required By:** #2 (Parser)

## Notes

First stage of compilation pipeline. Uses INDENT/DEDENT for Python-like significant whitespace.
