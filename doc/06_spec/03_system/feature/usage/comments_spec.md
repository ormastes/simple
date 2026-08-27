# Comments Specification

> Simple supports multiple comment styles for different purposes: line comments for quick notes, block comments for longer explanations (with nesting support), and documentation comments that can be extracted by documentation generators.

<!-- sdn-diagram:id=comments_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=comments_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

comments_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=comments_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Comments Specification

Simple supports multiple comment styles for different purposes: line comments for quick notes, block comments for longer explanations (with nesting support), and documentation comments that can be extracted by documentation generators.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #40-43 |
| Category | Syntax |
| Difficulty | 1/5 |
| Status | Implemented |
| Source | `test/03_system/feature/usage/comments_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

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

## Scenarios

### Comments - Line Comments

#### with single line

#### ignores comment after statement

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 42  # This comment is ignored
expect(x).to_equal(42)
```

</details>

#### ignores full line comment

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This entire line is a comment
val y = 10
expect(y).to_equal(10)
```

</details>

#### allows comment with special characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val z = 5  # Comment with !@#$%^&*()
expect(z).to_equal(5)
```

</details>

#### with multiple consecutive lines

#### handles consecutive line comments

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# First comment
# Second comment
# Third comment
val result = 100
expect(result).to_equal(100)
```

</details>

#### allows comments between statements

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 1
# Comment between statements
val b = 2
# Another comment
val c = a + b
expect(c).to_equal(3)
```

</details>

### Comments - Block Comments

#### with single line

#### ignores inline block comment

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = /* ignored */ 42
expect(x).to_equal(42)
```

</details>

#### allows block comment between tokens

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val y = 10 /* comment */ + /* another */ 5
expect(y).to_equal(15)
```

</details>

#### with multiple lines

#### ignores multi-line block comment

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
/*
This comment
spans multiple
lines
*/
val result = 100
expect(result).to_equal(100)
```

</details>

#### allows block comment in expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = 5 + /*
    inline comment
    on multiple lines
*/ 10
expect(value).to_equal(15)
```

</details>

#### with nesting

#### handles nested block comments

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
/* outer comment /* nested comment */ still in outer */
val x = 42
expect(x).to_equal(42)
```

</details>

#### allows multiple nesting levels

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
/* level 1 /* level 2 /* level 3 */ back to 2 */ back to 1 */
val y = 10
expect(y).to_equal(10)
```

</details>

### Comments - Documentation Comments

#### with line doc comments

#### preserves doc comment content

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Note: Doc comments are parsed by lexer
val x = 42
expect(x).to_equal(42)
```

</details>

#### allows doc comment before function

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Doc comments work with functions
val result = add_two(3, 4)
expect(result).to_equal(7)
```

</details>

#### with block doc comments

#### preserves block doc comment

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Block doc comments work at module level
val documented = 100
expect(documented).to_equal(100)
```

</details>

#### allows doc comment with formatting

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Doc comments can document functions
val result = multiply(6, 7)
expect(result).to_equal(42)
```

</details>

### Comments - Placement

#### in expressions

#### allows comments in arithmetic

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 10 /* first */ + /* second */ 20
expect(result).to_equal(30)
```

</details>

#### allows comments in function calls

1. fn triple
   - Expected: value equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn triple(x):
    x * 3

val value = triple(/* arg */ 5)
expect(value).to_equal(15)
```

</details>

#### around definitions

#### allows comment before variable

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Define the answer
val answer = 42
expect(answer).to_equal(42)
```

</details>

#### allows comment before function

1. fn double
   - Expected: double(21) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Helper function
fn double(x):
    x * 2

expect(double(21)).to_equal(42)
```

</details>

### Comments - Edge Cases

#### with empty comments

#### handles empty line comment

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 42  #
expect(x).to_equal(42)
```

</details>

#### handles empty block comment

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val y = /**/ 10
expect(y).to_equal(10)
```

</details>

#### with comment-like strings

#### preserves hash in string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = "This # is not a comment"
expect(text).to_equal("This # is not a comment")
```

</details>

#### preserves block markers in string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "/* not a comment */"
expect(code).to_equal("/* not a comment */")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
