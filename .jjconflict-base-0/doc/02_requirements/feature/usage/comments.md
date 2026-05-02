# Comments Specification
*Source:* `test/feature/usage/comments_spec.spl`
**Feature IDs:** #40-43  |  **Category:** Syntax  |  **Status:** Implemented

## Overview



## Overview

Simple supports multiple comment styles for different purposes: line comments for
quick notes, block comments for longer explanations (with nesting support), and
documentation comments that can be extracted by documentation generators.

## Syntax

### Line Comments

```simple
# This is a line comment
val x = 42  # Comment at end of line
```

### Block Comments

```simple
/* This is a block comment */
val y = 10

/*
Multi-line
block comment
*/
```

### Documentation Comments

```simple
## Single-line doc comment
fn example():
    pass

/**
 * Multi-line doc comment
 * With formatting
 */
struct Point:
    x: Int
    y: Int
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Line Comment | Single-line comment starting with `#` |
| Block Comment | Multi-line comment enclosed in `/* */` |
| Nested Comments | Block comments can contain other block comments |
| Doc Comment | Special comments for documentation generation |

## Behavior

- **Line comments** extend from `#` to end of line
- **Block comments** can span multiple lines and nest
- **Doc comments** are preserved and can be extracted
- Comments are ignored by the compiler (except doc comments)
- Comments do not affect code execution

## Related Specifications

- [Documentation Generation](../docgen/docgen_spec.md) - Using doc comments
- [Lexer](../lexer/lexer_spec.md) - Comment tokenization

## Implementation Notes

The lexer (`src/parser/src/lexer/comments.rs`) implements:
- Line comment skipping (skip until newline)
- Block comment nesting with depth tracking
- Doc comment content extraction and cleaning
- Triple-slash multi-line doc blocks

Performance: Comment parsing is O(n) where n is comment length.

## Examples

```simple
# Basic usage
val x = 42  # Initialize x

/* Block comment
   spanning multiple lines */
val y = x * 2

## Documentation for function
fn add(a, b):
    a + b

/**
 * Comprehensive documentation
 * with multiple lines
 */
struct Example:
    field: Int
```

## Feature: Comments - Line Comments

## Line Comment Syntax

    Line comments start with `#` and extend to the end of the line.
    They are completely ignored by the compiler.

### Scenario: with single line

### Scenario: Basic Line Comment

        A hash symbol begins a comment that lasts until newline.

        ```simple
        val x = 42  # This is ignored
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | ignores comment after statement | pass |
| 2 | ignores full line comment | pass |
| 3 | allows comment with special characters | pass |

**Example:** ignores comment after statement
    Given val x = 42  # This comment is ignored
    Then  expect(x).to_equal(42)

**Example:** ignores full line comment
    Given val y = 10
    Then  expect(y).to_equal(10)

**Example:** allows comment with special characters
    Given val z = 5  # Comment with !@#$%^&*()
    Then  expect(z).to_equal(5)

### Scenario: with multiple consecutive lines

### Scenario: Multiple Line Comments

        Each line needs its own `#` prefix.

| # | Example | Status |
|---|---------|--------|
| 1 | handles consecutive line comments | pass |
| 2 | allows comments between statements | pass |

**Example:** handles consecutive line comments
    Given val result = 100
    Then  expect(result).to_equal(100)

**Example:** allows comments between statements
    Given val a = 1
    Given val b = 2
    Given val c = a + b
    Then  expect(c).to_equal(3)

## Feature: Comments - Block Comments

## Block Comment Syntax

    Block comments are enclosed in `/* */` and can span multiple lines.
    Simple supports nested block comments for added flexibility.

### Scenario: with single line

### Scenario: Inline Block Comment

        Block comments can appear on a single line.

        ```simple
        val x = /* comment */ 42
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | ignores inline block comment | pass |
| 2 | allows block comment between tokens | pass |

**Example:** ignores inline block comment
    Given val x = /* ignored */ 42
    Then  expect(x).to_equal(42)

**Example:** allows block comment between tokens
    Given val y = 10 /* comment */ + /* another */ 5
    Then  expect(y).to_equal(15)

### Scenario: with multiple lines

### Scenario: Multi-line Block Comment

        Block comments can span multiple lines.

        ```simple
        /*
        This is a
        multi-line comment
        */
        val x = 42
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | ignores multi-line block comment | pass |
| 2 | allows block comment in expression | pass |

**Example:** ignores multi-line block comment
    Given val result = 100
    Then  expect(result).to_equal(100)

**Example:** allows block comment in expression
    Given val value = 5 + /*
    Then  expect(value).to_equal(15)

### Scenario: with nesting

### Scenario: Nested Block Comments

        Simple supports nested block comments, unlike C/C++.

        ```simple
        /* outer /* inner */ outer */
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | handles nested block comments | pass |
| 2 | allows multiple nesting levels | pass |

**Example:** handles nested block comments
    Given val x = 42
    Then  expect(x).to_equal(42)

**Example:** allows multiple nesting levels
    Given val y = 10
    Then  expect(y).to_equal(10)

## Feature: Comments - Documentation Comments

## Documentation Comment Syntax

    Doc comments are special comments that can be extracted for
    documentation generation. They use `##` or `/** */` syntax.

### Scenario: with line doc comments

### Scenario: Single-Line Doc Comment

        The `##` syntax creates a doc comment for the next item.

        ```simple
        ## This documents the function
        fn example():
            pass
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | preserves doc comment content | pass |
| 2 | allows doc comment before function | pass |

**Example:** preserves doc comment content
    Given val x = 42
    Then  expect(x).to_equal(42)

**Example:** allows doc comment before function
    Given val result = add_two(3, 4)
    Then  expect(result).to_equal(7)

### Scenario: with block doc comments

### Scenario: Multi-Line Doc Comment

        The `/** */` syntax creates multi-line documentation.

        ```simple
        /**
         * Comprehensive documentation
         * with multiple lines
         */
        fn example():
            pass
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | preserves block doc comment | pass |
| 2 | allows doc comment with formatting | pass |

**Example:** preserves block doc comment
    Given val documented = 100
    Then  expect(documented).to_equal(100)

**Example:** allows doc comment with formatting
    Given val result = multiply(6, 7)
    Then  expect(result).to_equal(42)

## Feature: Comments - Placement

## Comment Placement Rules

    Comments can appear in various locations within code.

### Scenario: in expressions

### Scenario: Comments Within Expressions

        Comments can appear between operators and operands.

| # | Example | Status |
|---|---------|--------|
| 1 | allows comments in arithmetic | pass |
| 2 | allows comments in function calls | pass |

**Example:** allows comments in arithmetic
    Given val result = 10 /* first */ + /* second */ 20
    Then  expect(result).to_equal(30)

**Example:** allows comments in function calls
    Given val value = triple(/* arg */ 5)
    Then  expect(value).to_equal(15)

### Scenario: around definitions

### Scenario: Comments Around Definitions

        Comments can document or explain definitions.

| # | Example | Status |
|---|---------|--------|
| 1 | allows comment before variable | pass |
| 2 | allows comment before function | pass |

**Example:** allows comment before variable
    Given val answer = 42
    Then  expect(answer).to_equal(42)

**Example:** allows comment before function
    Then  expect(double(21)).to_equal(42)

## Feature: Comments - Edge Cases

## Edge Case Handling

    Tests for unusual comment scenarios.

### Scenario: with empty comments

### Scenario: Empty Comment Content

        Comments can have no content after the marker.

| # | Example | Status |
|---|---------|--------|
| 1 | handles empty line comment | pass |
| 2 | handles empty block comment | pass |

**Example:** handles empty line comment
    Given val x = 42  #
    Then  expect(x).to_equal(42)

**Example:** handles empty block comment
    Given val y = /**/ 10
    Then  expect(y).to_equal(10)

### Scenario: with comment-like strings

### Scenario: Comment Syntax in Strings

        Comment markers inside strings are not treated as comments.

| # | Example | Status |
|---|---------|--------|
| 1 | preserves hash in string | pass |
| 2 | preserves block markers in string | pass |

**Example:** preserves hash in string
    Given val text = "This # is not a comment"
    Then  expect(text).to_equal("This # is not a comment")

**Example:** preserves block markers in string
    Given val code = "/* not a comment */"
    Then  expect(code).to_equal("/* not a comment */")


