# AST

*Source: `simple/std_lib/test/features/infrastructure/ast_spec.spl`*

---

# AST

**Feature ID:** #3
**Category:** Infrastructure
**Difficulty:** 3/5
**Status:** Complete

## Overview

Abstract Syntax Tree for all Simple language constructs. Parses literals, expressions, statements, patterns, and type annotations into structured tree representation.

## Syntax

The AST supports parsing:
- **Literals:** integers, floats, booleans, strings
- **Expressions:** binary operations, unary operations, function calls, indexing
- **Statements:** variable declarations, conditionals, loops, matches
- **Collections:** arrays, tuples, dictionaries
- **Type Annotations:** basic types, generic types
- **Functions:** function definitions with typed parameters and return types

## Implementation

**Files:**
- `src/parser/src/ast.rs`
- `src/parser/src/expressions/mod.rs`
- `src/parser/src/statements/mod.rs`

**Test Files:**
- `src/driver/tests/runner_tests.rs`

**Dependencies:** #1 (Lexer), #2 (Parser)
**Required By:** #4 (HIR)

## Notes

AST nodes use spans for error reporting. Pratt parser for expressions with correct precedence.
