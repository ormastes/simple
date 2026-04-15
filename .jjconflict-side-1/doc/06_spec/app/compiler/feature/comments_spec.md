# Comments Specification

**Feature ID:** #40-43 | **Category:** Syntax | **Difficulty:** 1/5 | **Status:** Implemented

_Source: `test/feature/usage/comments_spec.spl`_

---

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

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 23 |

## Test Structure

### Comments - Line Comments

#### with single line

- ✅ ignores comment after statement
- ✅ ignores full line comment
- ✅ allows comment with special characters
#### with multiple consecutive lines

- ✅ handles consecutive line comments
- ✅ allows comments between statements
### Comments - Block Comments

#### with single line

- ✅ ignores inline block comment
- ✅ allows block comment between tokens
#### with multiple lines

- ✅ ignores multi-line block comment
- ✅ allows block comment in expression
#### with nesting

- ✅ handles nested block comments
- ✅ allows multiple nesting levels
### Comments - Documentation Comments

#### with line doc comments

- ✅ preserves doc comment content
- ✅ allows doc comment before function
#### with block doc comments

- ✅ preserves block doc comment
- ✅ allows doc comment with formatting
### Comments - Placement

#### in expressions

- ✅ allows comments in arithmetic
- ✅ allows comments in function calls
#### around definitions

- ✅ allows comment before variable
- ✅ allows comment before function
### Comments - Edge Cases

#### with empty comments

- ✅ handles empty line comment
- ✅ handles empty block comment
#### with comment-like strings

- ✅ preserves hash in string
- ✅ preserves block markers in string

