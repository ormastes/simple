# Parser Edge Cases for Operators, Keywords, and Type Syntax

**Feature ID:** #PARSER-015 | **Category:** Syntax | **Status:** In Progress

_Source: `test/feature/usage/parser_edge_cases_spec.spl`_

---

## Overview

The Simple parser must handle several non-trivial syntactic forms that are easy to
mis-parse: the matrix-multiplication operator `@`, the keyword-style bitwise `xor`
operator, and bracket-based array type annotations `[T]`. This spec exercises each
form in isolation and in combination, verifying correct tokenisation, operator
precedence, and type annotation parsing. A `super` keyword test is planned but
commented out pending interpreter support for inheritance dispatch.

## Syntax

```simple
# Matrix multiplication operator (@)
val result = 3 @ 4          # => 12

# Bitwise XOR keyword operator
val bits = 5 xor 3          # => 6

# Array type annotations with square brackets
fn takes_array(items: [i64]) -> [i64]:
    return items

# Combined precedence
val c = (a xor b) @ 2       # xor first, then @
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| `@` operator | Matrix multiplication infix operator parsed as a binary expression |
| `xor` keyword operator | Bitwise XOR expressed as an alphabetic keyword, not a symbol |
| Array type syntax | `[T]` bracket notation used in parameter and return type positions |
| Operator precedence | Verifies correct evaluation order when `@` and `xor` appear together |

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 9 |

## Test Structure

### Parser Edge Cases

#### Matrix Multiplication Operator

- ✅ parses @ operator in expressions
- ✅ parses @ operator with variables
#### Bitwise XOR Keyword

- ✅ parses xor keyword in expressions
- ✅ parses xor keyword with variables
- ✅ parses xor in complex expressions
#### Array Type Syntax

- ✅ parses array types with square brackets
- ✅ parses array return types
#### Operator Precedence

- ✅ handles @ and xor together
- ✅ handles multiple operators

