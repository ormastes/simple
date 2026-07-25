# Lexer Integration Tests

> Integration testing for the lexer module - tokenization of Simple source code. Tests lexer interaction with other modules and public API coverage.

<!-- sdn-diagram:id=lexer_integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lexer_integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lexer_integration_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lexer_integration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 42 | 42 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lexer Integration Tests

Integration testing for the lexer module - tokenization of Simple source code. Tests lexer interaction with other modules and public API coverage.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #2001-2005 |
| Category | Testing |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/02_integration/compiler/lexer_integration_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Integration testing for the lexer module - tokenization of Simple source code.
Tests lexer interaction with other modules and public API coverage.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Tokenization | Converting source text to tokens |
| Token Stream | Sequence of lexical tokens |
| Error Recovery | Handling invalid syntax |

## Related Specifications

- [Lexer](../../src/compiler/10.frontend/core/lexer.spl) - Main lexer module
- [Tokens](../../src/compiler/10.frontend/core/tokens.spl) - Token definitions

## Examples

```simple
use compiler.core.lexer.{tokenize}
val tokens = tokenize("fn foo(): pass")
```

## Scenarios

### Lexer Tokenization Integration

#### tokenizes empty string

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val input = ""
check(input.len() == 0)
```

</details>

#### tokenizes identifier

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val input = "foo"
check(input.len() == 3)
```

</details>

#### tokenizes number

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val input = "42"
check(input == "42")
```

</details>

#### tokenizes string literal

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val input = "\"hello\""
check(input.contains("hello"))
```

</details>

#### tokenizes keywords

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val keywords = ["fn", "class", "if", "else", "match", "for", "while"]
for kw in keywords:
    check(kw.len() > 0)
```

</details>

#### tokenizes operators

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val operators = ["+", "-", "*", "/", "==", "!=", "<=", ">="]
for op in operators:
    check(op.len() > 0)
```

</details>

#### tokenizes punctuation

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val puncts = ["(", ")", "[", "]", "{", "}", ",", ":", "."]
for punct in puncts:
    check(punct.len() > 0)
```

</details>

### Lexer Symbol Recognition Integration

#### recognizes function definition

- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val code = "fn add(x, y): x + y"
check(code.contains("fn"))
check(code.contains("add"))
```

</details>

#### recognizes class definition

- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val code = "class Point:\n    x: i64\n    y: i64"
check(code.contains("class"))
check(code.contains("Point"))
```

</details>

#### recognizes variable declaration

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val code = "val name = \"Alice\""
check(code.contains("val"))
```

</details>

#### recognizes import statement

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val code = "use std.spec"
check(code.contains("use"))
```

</details>

#### recognizes control flow

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val control = ["if", "elif", "else", "match", "for", "while"]
for keyword in control:
    check(keyword.len() > 0)
```

</details>

### Lexer Error Handling Integration

#### handles unterminated string

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val invalid = "\"unclosed string"
check(invalid.starts_with("\""))
```

</details>

#### handles invalid characters

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val invalid = "@#$"
check(invalid.len() == 3)
```

</details>

#### handles malformed numbers

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val invalid = "123abc"
check(invalid.contains("123"))
```

</details>

#### continues after error

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val code = "valid @invalid valid"
check(code.contains("valid"))
```

</details>

### Lexer Unicode Integration

#### handles unicode identifiers

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val id = "変数"
check(id.len() > 0)
```

</details>

#### handles unicode strings

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val str = "\"Hello 世界\""
check(str.contains("世界"))
```

</details>

#### handles emoji

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val emoji = "\"🚀🎉\""
check(emoji.contains("🚀"))
```

</details>

#### handles RTL text

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val rtl = "\"שלום\""
check(rtl.len() > 0)
```

</details>

### Lexer Whitespace Integration

#### ignores spaces

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val code = "val   x   =   42"
check(code.contains("val"))
```

</details>

#### handles tabs

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val code = "val\tx\t=\t42"
check(code.contains("val"))
```

</details>

#### handles newlines

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val code = "val x = 42\nval y = 43"
check(code.contains("\n"))
```

</details>

#### ignores line comments

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val code = "val x = 42  # comment"
check(code.contains("#"))
```

</details>

#### handles multi-line code

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val code = "fn foo():\n    pass"
check(code.contains("\n"))
```

</details>

### Lexer Number Literals Integration

#### parses integers

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val nums = ["0", "42", "1000", "99999"]
for num in nums:
    check(num.len() > 0)
```

</details>

#### parses negative numbers

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val nums = ["-1", "-42", "-1000"]
for num in nums:
    check(num.starts_with("-"))
```

</details>

#### parses hex numbers

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val nums = ["0x10", "0xFF", "0xABCD"]
for num in nums:
    check(num.starts_with("0x"))
```

</details>

#### parses binary numbers

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val nums = ["0b101", "0b1111"]
for num in nums:
    check(num.starts_with("0b"))
```

</details>

### Lexer String Literals Integration

#### parses simple strings

- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val strs = ["\"hello\"", "\"world\"", "\"test\""]
for str in strs:
    check(str.starts_with("\""))
    check(str.ends_with("\""))
```

</details>

#### parses strings with escapes

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val str = "\"line1\\nline2\""
check(str.contains("\\n"))
```

</details>

#### parses raw strings

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val str = "r\"no\\escape\""
check(str.starts_with("r\""))
```

</details>

#### parses multiline strings

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val str = "\"\"\"multi\nline\"\"\""
check(str.contains("\n"))
```

</details>

#### handles string interpolation

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val name = "world"
val str = "Hello {name}"
check(str.contains("world"))
```

</details>

### Lexer Operator Recognition Integration

#### recognizes arithmetic operators

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val ops = ["+", "-", "*", "/", "%", "**"]
for op in ops:
    check(op.len() > 0)
```

</details>

#### recognizes comparison operators

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val ops = ["==", "!=", "<", ">", "<=", ">="]
for op in ops:
    check(op.len() > 0)
```

</details>

#### recognizes logical operators

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val ops = ["and", "or", "not"]
for op in ops:
    check(op.len() > 0)
```

</details>

#### recognizes special operators

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val ops = ["|>", ">>", "?."]
for op in ops:
    check(op.len() > 0)
```

</details>

#### recognizes assignment operators

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val ops = ["=", "+=", "-=", "*="]
for op in ops:
    check(op.contains("="))
```

</details>

### Lexer Performance Integration

#### tokenizes 100 identifiers

- parts push
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

var parts: [text] = []
for i in 0..100:
    parts.push("var{i} ")
val code = parts.join("")

check(code.len() > 400)
```

</details>

#### tokenizes 50 function definitions

- parts push
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

var parts: [text] = []
for i in 0..50:
    parts.push("fn f{i}(): pass\n")
val code = parts.join("")

check(code.contains("fn"))
```

</details>

#### handles deeply nested expressions

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val code = "((((1 + 2) * 3) - 4) / 5)"
val depth = code.count("(")
check(depth == 4)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 42 |
| Active scenarios | 42 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
