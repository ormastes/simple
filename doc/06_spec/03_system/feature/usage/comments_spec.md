# Comments Specification

> Simple supports multiple comment styles for different purposes: line comments for quick notes, block comments for longer explanations (with nesting support), and documentation comments that can be extracted by documentation generators.

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Simple supports multiple comment styles for different purposes: line comments for
quick notes, block comments for longer explanations (with nesting support), and
documentation comments that can be extracted by documentation generators.

## Syntax

### Line Comments

```simple
# This is a line comment
use std.spec.step

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

- ignores comment after statement
   - Expected: x equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("ignores comment after statement")
val x = 42  # This comment is ignored
expect(x).to_equal(42)
```

</details>

#### ignores full line comment

- ignores full line comment
   - Expected: y equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("ignores full line comment")
# This entire line is a comment
val y = 10
expect(y).to_equal(10)
```

</details>

#### allows comment with special characters

- allows comment with special characters
   - Expected: z equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows comment with special characters")
val z = 5  # Comment with !@#$%^&*()
expect(z).to_equal(5)
```

</details>

#### with multiple consecutive lines

#### handles consecutive line comments

- handles consecutive line comments
   - Expected: result equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles consecutive line comments")
# First comment
# Second comment
# Third comment
val result = 100
expect(result).to_equal(100)
```

</details>

#### allows comments between statements

- allows comments between statements
   - Expected: c equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows comments between statements")
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

- ignores inline block comment
   - Expected: x equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("ignores inline block comment")
val x = /* ignored */ 42
expect(x).to_equal(42)
```

</details>

#### allows block comment between tokens

- allows block comment between tokens
   - Expected: y equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows block comment between tokens")
val y = 10 /* comment */ + /* another */ 5
expect(y).to_equal(15)
```

</details>

#### with multiple lines

#### ignores multi-line block comment

- ignores multi-line block comment
   - Expected: result equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("ignores multi-line block comment")
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

- allows block comment in expression
   - Expected: value equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows block comment in expression")
val value = 5 + /*
    inline comment
    on multiple lines
*/ 10
expect(value).to_equal(15)
```

</details>

#### with nesting

#### handles nested block comments

- handles nested block comments
   - Expected: x equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles nested block comments")
/* outer comment /* nested comment */ still in outer */
val x = 42
expect(x).to_equal(42)
```

</details>

#### allows multiple nesting levels

- allows multiple nesting levels
   - Expected: y equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows multiple nesting levels")
/* level 1 /* level 2 /* level 3 */ back to 2 */ back to 1 */
val y = 10
expect(y).to_equal(10)
```

</details>

### Comments - Documentation Comments

#### with line doc comments

#### preserves doc comment content

- preserves doc comment content
   - Expected: x equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preserves doc comment content")
# Note: Doc comments are parsed by lexer
val x = 42
expect(x).to_equal(42)
```

</details>

#### allows doc comment before function

- allows doc comment before function
   - Expected: result equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows doc comment before function")
# Doc comments work with functions
val result = add_two(3, 4)
expect(result).to_equal(7)
```

</details>

#### with block doc comments

#### preserves block doc comment

- preserves block doc comment
   - Expected: documented equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preserves block doc comment")
# Block doc comments work at module level
val documented = 100
expect(documented).to_equal(100)
```

</details>

#### allows doc comment with formatting

- allows doc comment with formatting
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows doc comment with formatting")
# Doc comments can document functions
val result = multiply(6, 7)
expect(result).to_equal(42)
```

</details>

### Comments - Placement

#### in expressions

#### allows comments in arithmetic

- allows comments in arithmetic
   - Expected: result equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows comments in arithmetic")
val result = 10 /* first */ + /* second */ 20
expect(result).to_equal(30)
```

</details>

#### allows comments in function calls

- allows comments in function calls
   - Expected: value equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows comments in function calls")
fn triple(x):
    x * 3

val value = triple(/* arg */ 5)
expect(value).to_equal(15)
```

</details>

#### around definitions

#### allows comment before variable

- allows comment before variable
   - Expected: answer equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows comment before variable")
# Define the answer
val answer = 42
expect(answer).to_equal(42)
```

</details>

#### allows comment before function

- allows comment before function
   - Expected: double(21) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows comment before function")
# Helper function
fn double(x):
    x * 2

expect(double(21)).to_equal(42)
```

</details>

### Comments - Edge Cases

#### with empty comments

#### handles empty line comment

- handles empty line comment
   - Expected: x equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles empty line comment")
val x = 42  #
expect(x).to_equal(42)
```

</details>

#### handles empty block comment

- handles empty block comment
   - Expected: y equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles empty block comment")
val y = /**/ 10
expect(y).to_equal(10)
```

</details>

#### with comment-like strings

#### preserves hash in string

- preserves hash in string
   - Expected: text equals `This # is not a comment`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preserves hash in string")
val text = "This # is not a comment"
expect(text).to_equal("This # is not a comment")
```

</details>

#### preserves block markers in string

- preserves block markers in string
   - Expected: code equals `/* not a comment */`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preserves block markers in string")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e602eb5069fefc0b008893249ebd24a4b4f48169f80fafb66b1e39a38bfa0f86`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e602eb5069fefc0b008893249ebd24a4b4f48169f80fafb66b1e39a38bfa0f86`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e602eb5069fefc0b008893249ebd24a4b4f48169f80fafb66b1e39a38bfa0f86`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/feature/usage/comments_spec.spl
mirror: doc/06_spec/03_system/feature/usage/comments_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/comments_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/comments_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/comments_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 21 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/usage/comments_spec.spl:135:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ignores comment after statement' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/comments_spec.spl:141:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ignores full line comment' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/comments_spec.spl:148:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows comment with special characters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
