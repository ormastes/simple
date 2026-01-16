*Source: `simple/test/system/features/comments/comments_spec.spl`*
*Last Updated: 2026-01-16*

---

# Comments Specification

**Feature IDs:** #40-43
**Category:** Syntax
**Difficulty:** 1/5
**Status:** Implemented

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

## Line Comment Syntax

    Line comments start with `#` and extend to the end of the line.
    They are completely ignored by the compiler.

### Scenario: Basic Line Comment

        A hash symbol begins a comment that lasts until newline.

        ```simple
        val x = 42  # This is ignored
        ```

### Scenario: Multiple Line Comments

        Each line needs its own `#` prefix.

## Block Comment Syntax

    Block comments are enclosed in `/* */` and can span multiple lines.
    Simple supports nested block comments for added flexibility.

### Scenario: Inline Block Comment

        Block comments can appear on a single line.

        ```simple
        val x = /* comment */ 42
        ```

### Scenario: Multi-line Block Comment

        Block comments can span multiple lines.

        ```simple
        /*
        This is a
        multi-line comment
        */
        val x = 42
        ```

### Scenario: Nested Block Comments

        Simple supports nested block comments, unlike C/C++.

        ```simple
        /* outer /* inner */ outer */
        ```

## Documentation Comment Syntax

    Doc comments are special comments that can be extracted for
    documentation generation. They use `##` or `/** */` syntax.

### Scenario: Single-Line Doc Comment

        The `##` syntax creates a doc comment for the next item.

        ```simple
        ## This documents the function
        fn example():
            pass
        ```

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

## Comment Placement Rules

    Comments can appear in various locations within code.

### Scenario: Comments Within Expressions

        Comments can appear between operators and operands.

### Scenario: Comments Around Definitions

        Comments can document or explain definitions.

## Edge Case Handling

    Tests for unusual comment scenarios.

### Scenario: Empty Comment Content

        Comments can have no content after the marker.

### Scenario: Comment Syntax in Strings

        Comment markers inside strings are not treated as comments.
