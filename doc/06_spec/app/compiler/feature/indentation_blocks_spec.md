# Indentation-Based Blocks Specification

**Feature ID:** #840-845 | **Category:** Syntax | **Difficulty:** 2/5 | **Status:** Implemented

_Source: `test/feature/usage/indentation_blocks_spec.spl`_

---

## Overview

Indentation-based blocks use Python-style significant whitespace to delimit code blocks
instead of braces. This feature provides clean, readable syntax for function bodies,
control flow, and other block-structured code in Simple.

## Syntax

```simple
# Function body indentation
fn add(a: i64, b: i64) -> i64:
    a + b

# Control flow indentation
if condition:
    do_something()
else:
    do_alternative()

# Nested indentation
loop:
    if inner_condition:
        process()
        continue
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Indentation | Whitespace level determines block scope |
| Dedentation | Return to previous indentation level |
| Colon | Marks beginning of indented block |
| Continuation | Lines can continue to next with indentation |

## Behavior

- Indentation level determines block membership
- Consistent indentation required within a block
- Tab and space mixing is not allowed
- Indentation can use either tabs or spaces (configured at parse)
- Dedentation marks end of block and returns to outer scope

## Related Specifications

- [Lexer](../lexer/lexer_spec.spl) - Token recognition including indentation
- [Parser](../parser/parser_spec.spl) - Block structure parsing
- [Syntax](../syntax/syntax_spec.spl) - Language syntax overview

## Implementation Notes

Indentation handling in lexer:
- Track indentation stack as separate token stream
- INDENT token marks increase in indentation
- DEDENT token marks decrease in indentation
- Implicit DEDENT at end of file if needed
- Error on inconsistent indentation mixing

## Examples

```simple
# Multi-level nested blocks
fn process_data(items: List<Int>) -> i64:
    var total = 0
    for item in items:
        if item > 0:
            total = total + item
        else:
            total = total - item
    total
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 15 |

## Test Structure

### Indentation Blocks - Basic

#### with function body indentation

- ✅ recognizes indented function body
#### with nested function bodies

- ✅ handles nested function definitions
### Indentation Blocks - Control Flow

#### with if-else blocks

- ✅ handles if-else indentation
#### with loop blocks

- ✅ handles loop indentation
#### with nested control flow

- ✅ handles nested control flow
### Indentation Blocks - Multiple Statements

#### with sequential statements

- ✅ executes multiple statements
#### with mixed statement types

- ✅ mixes different statement types
### Indentation Blocks - Consistency

#### with consistent indentation

- ✅ maintains block indentation
#### with dedentation

- ✅ terminates block on dedent
### Indentation Blocks - Complex Nesting

#### with deeply nested blocks

- ✅ handles deep nesting
#### with mixed block types

- ✅ mixes nested block types
### Indentation Blocks - Expressions

#### with conditional expressions

- ✅ handles if expression indentation
#### with block values

- ✅ uses indented blocks as values
### Indentation Blocks - Edge Cases

#### with empty blocks

- ✅ handles empty block
#### with single statement blocks

- ✅ handles single-statement block

