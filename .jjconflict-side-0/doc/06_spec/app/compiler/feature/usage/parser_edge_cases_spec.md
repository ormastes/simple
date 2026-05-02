# Parser Edge Cases for Operators, Keywords, and Type Syntax

The Simple parser must handle several non-trivial syntactic forms that are easy to mis-parse: the matrix-multiplication operator `@`, the keyword-style bitwise `xor` operator, and bracket-based array type annotations `[T]`. This spec exercises each form in isolation and in combination, verifying correct tokenisation, operator precedence, and type annotation parsing. A `super` keyword test is planned but commented out pending interpreter support for inheritance dispatch.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-015 |
| Category | Syntax |
| Status | In Progress |
| Source | `test/feature/usage/parser_edge_cases_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

The Simple parser must handle several non-trivial syntactic forms that are easy to
mis-parse: the matrix-multiplication operator `@`, the keyword-style bitwise `xor`
operator, and bracket-based array type annotations `[T]`. This spec exercises each
form in isolation and in combination, verifying correct tokenisation, operator
precedence, and type annotation parsing. A `super` keyword test is planned but
commented out pending interpreter support for inheritance dispatch.

## Syntax

```simple
val result = 3 @ 4          # => 12

val bits = 5 xor 3          # => 6

fn takes_array(items: [i64]) -> [i64]:
return items

val c = (a xor b) @ 2       # xor first, then @
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| `@` operator | Matrix multiplication infix operator parsed as a binary expression |
| `xor` keyword operator | Bitwise XOR expressed as an alphabetic keyword, not a symbol |
| Array type syntax | `[T]` bracket notation used in parameter and return type positions |
| Operator precedence | Verifies correct evaluation order when `@` and `xor` appear together |

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/parser_edge_cases/result.json` |

## Scenarios

- parses @ operator in expressions
- parses @ operator with variables
- parses xor keyword in expressions
- parses xor keyword with variables
- parses xor in complex expressions
- parses array types with square brackets
- parses array return types
- handles @ and xor together
- handles multiple operators
