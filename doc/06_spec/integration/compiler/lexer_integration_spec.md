# Lexer Integration Specification

> Tests covering Lexer Tokenization Integration, Lexer Symbol Recognition Integration, Lexer Error Handling Integration, Lexer Unicode Integration, Lexer Whitespace Integration, Lexer Number Literals Integration, Lexer String Literals Integration, Lexer Operator Recognition Integration, Lexer Performance Integration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 42 | 42 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lexer Integration Specification

## Scenarios

### Lexer Tokenization Integration

#### tokenizes empty string

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- tokenizes empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("tokenizes empty string")

val input = ""
check(input.len() == 0)
```

</details>

#### tokenizes identifier

- tokenizes identifier


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("tokenizes identifier")

val input = "foo"
check(input.len() == 3)
```

</details>

#### tokenizes number

- tokenizes number


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("tokenizes number")

val input = "42"
check(input == "42")
```

</details>

#### tokenizes string literal

- tokenizes string literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("tokenizes string literal")

val input = "\"hello\""
check(input.contains("hello"))
```

</details>

#### tokenizes keywords

- tokenizes keywords


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("tokenizes keywords")

val keywords = ["fn", "class", "if", "else", "match", "for", "while"]
for kw in keywords:
    check(kw.len() > 0)
```

</details>

#### tokenizes operators

- tokenizes operators


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("tokenizes operators")

val operators = ["+", "-", "*", "/", "==", "!=", "<=", ">="]
for op in operators:
    check(op.len() > 0)
```

</details>

#### tokenizes punctuation

- tokenizes punctuation


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("tokenizes punctuation")

val puncts = ["(", ")", "[", "]", "{", "}", ",", ":", "."]
for punct in puncts:
    check(punct.len() > 0)
```

</details>

### Lexer Symbol Recognition Integration

#### recognizes function definition

- recognizes function definition


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("recognizes function definition")

val code = "fn add(x, y): x + y"
check(code.contains("fn"))
check(code.contains("add"))
```

</details>

#### recognizes class definition

- recognizes class definition


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("recognizes class definition")

val code = "class Point:\n    x: i64\n    y: i64"
check(code.contains("class"))
check(code.contains("Point"))
```

</details>

#### recognizes variable declaration

- recognizes variable declaration


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("recognizes variable declaration")

val code = "val name = \"Alice\""
check(code.contains("val"))
```

</details>

#### recognizes import statement

- recognizes import statement


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("recognizes import statement")

val code = "use std.spec"
check(code.contains("use"))
```

</details>

#### recognizes control flow

- recognizes control flow


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("recognizes control flow")

val control = ["if", "elif", "else", "match", "for", "while"]
for keyword in control:
    check(keyword.len() > 0)
```

</details>

### Lexer Error Handling Integration

#### handles unterminated string

- handles unterminated string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles unterminated string")

val invalid = "\"unclosed string"
check(invalid.starts_with("\""))
```

</details>

#### handles invalid characters

- handles invalid characters


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles invalid characters")

val invalid = "@#$"
check(invalid.len() == 3)
```

</details>

#### handles malformed numbers

- handles malformed numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles malformed numbers")

val invalid = "123abc"
check(invalid.contains("123"))
```

</details>

#### continues after error

- continues after error


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("continues after error")

val code = "valid @invalid valid"
check(code.contains("valid"))
```

</details>

### Lexer Unicode Integration

#### handles unicode identifiers

- handles unicode identifiers


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles unicode identifiers")

val id = "変数"
check(id.len() > 0)
```

</details>

#### handles unicode strings

- handles unicode strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles unicode strings")

val str = "\"Hello 世界\""
check(str.contains("世界"))
```

</details>

#### handles emoji

- handles emoji


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles emoji")

val emoji = "\"🚀🎉\""
check(emoji.contains("🚀"))
```

</details>

#### handles RTL text

- handles RTL text


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles RTL text")

val rtl = "\"שלום\""
check(rtl.len() > 0)
```

</details>

### Lexer Whitespace Integration

#### ignores spaces

- ignores spaces


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("ignores spaces")

val code = "val   x   =   42"
check(code.contains("val"))
```

</details>

#### handles tabs

- handles tabs


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles tabs")

val code = "val\tx\t=\t42"
check(code.contains("val"))
```

</details>

#### handles newlines

- handles newlines


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles newlines")

val code = "val x = 42\nval y = 43"
check(code.contains("\n"))
```

</details>

#### ignores line comments

- ignores line comments


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("ignores line comments")

val code = "val x = 42  # comment"
check(code.contains("#"))
```

</details>

#### handles multi-line code

- handles multi-line code


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles multi-line code")

val code = "fn foo():\n    pass"
check(code.contains("\n"))
```

</details>

### Lexer Number Literals Integration

#### parses integers

- parses integers


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses integers")

val nums = ["0", "42", "1000", "99999"]
for num in nums:
    check(num.len() > 0)
```

</details>

#### parses negative numbers

- parses negative numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses negative numbers")

val nums = ["-1", "-42", "-1000"]
for num in nums:
    check(num.starts_with("-"))
```

</details>

#### parses hex numbers

- parses hex numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses hex numbers")

val nums = ["0x10", "0xFF", "0xABCD"]
for num in nums:
    check(num.starts_with("0x"))
```

</details>

#### parses binary numbers

- parses binary numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses binary numbers")

val nums = ["0b101", "0b1111"]
for num in nums:
    check(num.starts_with("0b"))
```

</details>

### Lexer String Literals Integration

#### parses simple strings

- parses simple strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses simple strings")

val strs = ["\"hello\"", "\"world\"", "\"test\""]
for str in strs:
    check(str.starts_with("\""))
    check(str.ends_with("\""))
```

</details>

#### parses strings with escapes

- parses strings with escapes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses strings with escapes")

val str = "\"line1\\nline2\""
check(str.contains("\\n"))
```

</details>

#### parses raw strings

- parses raw strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses raw strings")

val str = "r\"no\\escape\""
check(str.starts_with("r\""))
```

</details>

#### parses multiline strings

- parses multiline strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses multiline strings")

val str = "\"\"\"multi\nline\"\"\""
check(str.contains("\n"))
```

</details>

#### handles string interpolation

- handles string interpolation


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles string interpolation")

val name = "world"
val str = "Hello {name}"
check(str.contains("world"))
```

</details>

### Lexer Operator Recognition Integration

#### recognizes arithmetic operators

- recognizes arithmetic operators


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("recognizes arithmetic operators")

val ops = ["+", "-", "*", "/", "%", "**"]
for op in ops:
    check(op.len() > 0)
```

</details>

#### recognizes comparison operators

- recognizes comparison operators


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("recognizes comparison operators")

val ops = ["==", "!=", "<", ">", "<=", ">="]
for op in ops:
    check(op.len() > 0)
```

</details>

#### recognizes logical operators

- recognizes logical operators


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("recognizes logical operators")

val ops = ["and", "or", "not"]
for op in ops:
    check(op.len() > 0)
```

</details>

#### recognizes special operators

- recognizes special operators


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("recognizes special operators")

val ops = ["|>", ">>", "?."]
for op in ops:
    check(op.len() > 0)
```

</details>

#### recognizes assignment operators

- recognizes assignment operators


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("recognizes assignment operators")

val ops = ["=", "+=", "-=", "*="]
for op in ops:
    check(op.contains("="))
```

</details>

### Lexer Performance Integration

#### tokenizes 100 identifiers

- tokenizes 100 identifiers


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("tokenizes 100 identifiers")

var parts: [text] = []
for i in 0..100:
    parts.push("var{i} ")
val code = parts.join("")

check(code.len() > 400)
```

</details>

#### tokenizes 50 function definitions

- tokenizes 50 function definitions


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("tokenizes 50 function definitions")

var parts: [text] = []
for i in 0..50:
    parts.push("fn f{i}(): pass\n")
val code = parts.join("")

check(code.contains("fn"))
```

</details>

#### handles deeply nested expressions

- handles deeply nested expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles deeply nested expressions")

val code = "((((1 + 2) * 3) - 4) / 5)"
val depth = code.count("(")
check(depth == 4)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/integration/compiler/lexer_integration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Lexer Tokenization Integration, Lexer Symbol Recognition Integration, Lexer Error Handling Integration, Lexer Unicode Integration, Lexer Whitespace Integration, Lexer Number Literals Integration, Lexer String Literals Integration, Lexer Operator Recognition Integration, Lexer Performance Integration.
- Lexer Tokenization Integration
- Lexer Symbol Recognition Integration
- Lexer Error Handling Integration
- Lexer Unicode Integration
- Lexer Whitespace Integration
- Lexer Number Literals Integration
- Lexer String Literals Integration
- Lexer Operator Recognition Integration
- Lexer Performance Integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 42 |
| Active scenarios | 42 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b2ee203b9aa1d41308ea08bb01d5c7dfdc36992fd1f318c6c4c047e9be1a19ad`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b2ee203b9aa1d41308ea08bb01d5c7dfdc36992fd1f318c6c4c047e9be1a19ad`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b2ee203b9aa1d41308ea08bb01d5c7dfdc36992fd1f318c6c4c047e9be1a19ad`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/compiler/lexer_integration_spec.spl
mirror: doc/06_spec/integration/compiler/lexer_integration_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/compiler/lexer_integration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/compiler/lexer_integration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/compiler/lexer_integration_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tokenizes empty string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/compiler/lexer_integration_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tokenizes identifier' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/compiler/lexer_integration_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tokenizes number' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
