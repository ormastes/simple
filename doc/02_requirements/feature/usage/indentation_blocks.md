# Indentation-Based Blocks Specification
*Source:* `test/feature/usage/indentation_blocks_spec.spl`
**Feature IDs:** #840-845  |  **Category:** Syntax  |  **Status:** Implemented

## Overview



use std.text.{NL}

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

## Feature: Indentation Blocks - Basic

## Basic Indentation and Block Scoping

    Tests basic indentation-based block structure.

### Scenario: with function body indentation

### Scenario: Function Block Scope

        Function bodies are indented blocks following the function signature.

| # | Example | Status |
|---|---------|--------|
| 1 | recognizes indented function body | pass |

**Example:** recognizes indented function body
    Then  expect simple() == 42

### Scenario: with nested function bodies

### Scenario: Nested Function Definitions

        Functions can be nested with proper indentation.

| # | Example | Status |
|---|---------|--------|
| 1 | handles nested function definitions | pass |

**Example:** handles nested function definitions
    Then  expect outer() == 10

## Feature: Indentation Blocks - Control Flow

## Control Flow Block Structure

    Tests indentation blocks in control flow statements.

### Scenario: with if-else blocks

### Scenario: Conditional Block Indentation

        If and else blocks use indentation for body delimitation.

| # | Example | Status |
|---|---------|--------|
| 1 | handles if-else indentation | pass |

**Example:** handles if-else indentation
    Then  expect check_positive(5) == "positive"
    Then  expect check_positive(-3) == "non-positive"

### Scenario: with loop blocks

### Scenario: Loop Body Indentation

        Loop bodies are indented blocks.

| # | Example | Status |
|---|---------|--------|
| 1 | handles loop indentation | pass |

**Example:** handles loop indentation
    Given var sum = 0
    Given var i = 0
    Then  expect count_up(5) == 10  # 0+1+2+3+4

### Scenario: with nested control flow

### Scenario: Nested Control Structures

        Control structures can be nested with proper indentation.

| # | Example | Status |
|---|---------|--------|
| 1 | handles nested control flow | pass |

**Example:** handles nested control flow
    Given var sum = 0
    Given var i = 0
    Given var j = 0
    Then  expect matrix_sum(3) == 9  # 3x3 matrix

## Feature: Indentation Blocks - Multiple Statements

## Multiple Statements in Indented Blocks

    Tests blocks containing multiple statements.

### Scenario: with sequential statements

### Scenario: Statement Sequence

        Multiple statements in sequence within a block.

| # | Example | Status |
|---|---------|--------|
| 1 | executes multiple statements | pass |

**Example:** executes multiple statements
    Given var x = 1
    Given var y = 2
    Given var z = 3
    Then  expect multi_statement() == 6

### Scenario: with mixed statement types

### Scenario: Mixed Statements

        Blocks can contain assignments, calls, and expressions.

| # | Example | Status |
|---|---------|--------|
| 1 | mixes different statement types | pass |

**Example:** mixes different statement types
    Given var result = 0
    Then  expect mixed_statements(10) == 25

## Feature: Indentation Blocks - Consistency

## Indentation Consistency Checking

    Tests proper indentation level management.

### Scenario: with consistent indentation

### Scenario: Valid Indentation Levels

        All statements in a block maintain the same indentation.

| # | Example | Status |
|---|---------|--------|
| 1 | maintains block indentation | pass |

**Example:** maintains block indentation
    Given var a = 1
    Given var b = 2
    Given var c = 3
    Then  expect consistent_indent() == 6

### Scenario: with dedentation

### Scenario: Block Termination

        Dedentation correctly terminates blocks.

| # | Example | Status |
|---|---------|--------|
| 1 | terminates block on dedent | pass |

**Example:** terminates block on dedent
    Then  expect outer() == 15

## Feature: Indentation Blocks - Complex Nesting

## Complex Nested Block Structures

    Tests deeply nested indented blocks.

### Scenario: with deeply nested blocks

### Scenario: Multiple Nesting Levels

        Structures with several levels of nesting.

| # | Example | Status |
|---|---------|--------|
| 1 | handles deep nesting | pass |

**Example:** handles deep nesting
    Given var sum = 0
    Given var i = 0
    Given var j = 0
    Given var k = 0
    Then  expect deep_nest() == 8  # 2^3

### Scenario: with mixed block types

### Scenario: Nested Different Block Types

        Functions, conditionals, and loops nested together.

| # | Example | Status |
|---|---------|--------|
| 1 | mixes nested block types | pass |

**Example:** mixes nested block types
    Given var total = 0
    Given var i = 0
    Then  expect mixed_nesting() == 5  # compute(0)=1 + compute(1)=2 + compute(2)=3

## Feature: Indentation Blocks - Expressions

## Indented Block Expressions

    Tests indentation in expression contexts.

### Scenario: with conditional expressions

### Scenario: If Expression Indentation

        If expressions with indented branches.

| # | Example | Status |
|---|---------|--------|
| 1 | handles if expression indentation | pass |

**Example:** handles if expression indentation
    Given val result = if x > 0:
    Then  expect if_expr(5) == 10

### Scenario: with block values

### Scenario: Indented Value Blocks

        Indented blocks that produce values.

| # | Example | Status |
|---|---------|--------|
| 1 | uses indented blocks as values | pass |

**Example:** uses indented blocks as values
    Given val x = 5
    Given val y =
    Then  expect block_value() == 8

## Feature: Indentation Blocks - Edge Cases

## Edge Case Handling

    Tests edge cases in indentation handling.

### Scenario: with empty blocks

### Scenario: Empty Indented Block

        Blocks with no statements.

| # | Example | Status |
|---|---------|--------|
| 1 | handles empty block | pass |

### Scenario: with single statement blocks

### Scenario: Single-Statement Block

        Blocks containing only one statement.

| # | Example | Status |
|---|---------|--------|
| 1 | handles single-statement block | pass |

**Example:** handles single-statement block
    Then  expect single_stmt() == 42


