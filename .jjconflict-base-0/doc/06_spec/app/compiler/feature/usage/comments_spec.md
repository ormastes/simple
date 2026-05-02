# Comments Specification

Simple supports multiple comment styles for different purposes: line comments for quick notes, block comments for longer explanations (with nesting support), and documentation comments that can be extracted by documentation generators.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #40-43 |
| Category | Syntax |
| Difficulty | 1/5 |
| Status | Implemented |
| Source | `test/feature/usage/comments_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Simple supports multiple comment styles for different purposes: line comments for
quick notes, block comments for longer explanations (with nesting support), and
documentation comments that can be extracted by documentation generators.

## Syntax

### Line Comments

```simple
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

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/comments/result.json` |

## Scenarios

- ignores comment after statement
- ignores full line comment
- allows comment with special characters
- handles consecutive line comments
- allows comments between statements
- ignores inline block comment
- allows block comment between tokens
- ignores multi-line block comment
- allows block comment in expression
- handles nested block comments
- allows multiple nesting levels
- preserves doc comment content
- allows doc comment before function
- preserves block doc comment
- allows doc comment with formatting
- allows comments in arithmetic
- allows comments in function calls
- allows comment before variable
- allows comment before function
- handles empty line comment
- handles empty block comment
- preserves hash in string
- preserves block markers in string
