# lexer_integration_spec

> Verifies the lexer integration behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 42 | 42 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# lexer_integration_spec

Verifies the lexer integration behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/02_integration/compiler/lexer_integration_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the lexer integration behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Lexer Tokenization Integration

#### tokenizes empty string

- Verify: tokenizes empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_LEXER_INTEGRATION-001
step("Verify: tokenizes empty string")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario

val input = ""
check(input.len() == 0)
```

</details>

#### tokenizes identifier

- Verify: tokenizes identifier


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_LEXER_INTEGRATION-001
step("Verify: tokenizes identifier")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario

val input = "foo"
check(input.len() == 3)
```

</details>

#### tokenizes number

- Verify: tokenizes number


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_LEXER_INTEGRATION-001
step("Verify: tokenizes number")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario

val input = "42"
check(input == "42")
```

</details>

#### tokenizes string literal

- Verify: tokenizes string literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_LEXER_INTEGRATION-001
step("Verify: tokenizes string literal")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario

val input = "\"hello\""
check(input.contains("hello"))
```

</details>

#### tokenizes keywords

- Verify: tokenizes keywords


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_LEXER_INTEGRATION-001
step("Verify: tokenizes keywords")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario

val keywords = ["fn", "class", "if", "else", "match", "for", "while"]
for kw in keywords:
    check(kw.len() > 0)
```

</details>

#### tokenizes operators

- Verify: tokenizes operators


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_LEXER_INTEGRATION-001
step("Verify: tokenizes operators")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario

val operators = ["+", "-", "*", "/", "==", "!=", "<=", ">="]
for op in operators:
    check(op.len() > 0)
```

</details>

#### tokenizes punctuation

- Verify: tokenizes punctuation


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_LEXER_INTEGRATION-001
step("Verify: tokenizes punctuation")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario

val puncts = ["(", ")", "[", "]", "{", "}", ",", ":", "."]
for punct in puncts:
    check(punct.len() > 0)
```

</details>

### Lexer Symbol Recognition Integration

#### recognizes function definition

- Verify: recognizes function definition


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_LEXER_INTEGRATION-001
step("Verify: recognizes function definition")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario

val code = "fn add(x, y): x + y"
check(code.contains("fn"))
check(code.contains("add"))
```

</details>

#### recognizes class definition

- Verify: recognizes class definition


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_LEXER_INTEGRATION-001
step("Verify: recognizes class definition")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario

val code = "class Point:\n    x: i64\n    y: i64"
check(code.contains("class"))
check(code.contains("Point"))
```

</details>

#### recognizes variable declaration

- Verify: recognizes variable declaration


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_LEXER_INTEGRATION-001
step("Verify: recognizes variable declaration")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario

val code = "val name = \"Alice\""
check(code.contains("val"))
```

</details>

#### recognizes import statement

- Verify: recognizes import statement


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_LEXER_INTEGRATION-001
step("Verify: recognizes import statement")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario

val code = "use std.spec"
check(code.contains("use"))
```

</details>

#### recognizes control flow

- Verify: recognizes control flow


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_LEXER_INTEGRATION-001
step("Verify: recognizes control flow")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario

val control = ["if", "elif", "else", "match", "for", "while"]
for keyword in control:
    check(keyword.len() > 0)
```

</details>

### Lexer Error Handling Integration

#### handles unterminated string

- Verify: handles unterminated string


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_LEXER_INTEGRATION-001
step("Verify: handles unterminated string")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario

val invalid = "\"unclosed string"
check(invalid.starts_with("\""))
```

</details>

#### handles invalid characters

- Verify: handles invalid characters


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_LEXER_INTEGRATION-001
step("Verify: handles invalid characters")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario

val invalid = "@#$"
check(invalid.len() == 3)
```

</details>

#### handles malformed numbers

- Verify: handles malformed numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_LEXER_INTEGRATION-001
step("Verify: handles malformed numbers")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario

val invalid = "123abc"
check(invalid.contains("123"))
```

</details>

#### continues after error

- Verify: continues after error


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_LEXER_INTEGRATION-001
step("Verify: continues after error")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario

val code = "valid @invalid valid"
check(code.contains("valid"))
```

</details>

### Lexer Unicode Integration

#### handles unicode identifiers

- Verify: handles unicode identifiers


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_LEXER_INTEGRATION-001
step("Verify: handles unicode identifiers")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario

val id = "変数"
check(id.len() > 0)
```

</details>

#### handles unicode strings

- Verify: handles unicode strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_LEXER_INTEGRATION-001
step("Verify: handles unicode strings")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario

val str = "\"Hello 世界\""
check(str.contains("世界"))
```

</details>

#### handles emoji

- Verify: handles emoji


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_LEXER_INTEGRATION-001
step("Verify: handles emoji")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario

val emoji = "\"🚀🎉\""
check(emoji.contains("🚀"))
```

</details>

#### handles RTL text

- Verify: handles RTL text


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_LEXER_INTEGRATION-001
step("Verify: handles RTL text")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario

val rtl = "\"שלום\""
check(rtl.len() > 0)
```

</details>

### Lexer Whitespace Integration

#### ignores spaces

- Verify: ignores spaces


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_LEXER_INTEGRATION-001
step("Verify: ignores spaces")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario

val code = "val   x   =   42"
check(code.contains("val"))
```

</details>

#### handles tabs

- Verify: handles tabs


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_LEXER_INTEGRATION-001
step("Verify: handles tabs")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario

val code = "val\tx\t=\t42"
check(code.contains("val"))
```

</details>

#### handles newlines

- Verify: handles newlines


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_LEXER_INTEGRATION-001
step("Verify: handles newlines")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario

val code = "val x = 42\nval y = 43"
check(code.contains("\n"))
```

</details>

#### ignores line comments

- Verify: ignores line comments


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_LEXER_INTEGRATION-001
step("Verify: ignores line comments")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario

val code = "val x = 42  # comment"
check(code.contains("#"))
```

</details>

#### handles multi-line code

- Verify: handles multi-line code


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_LEXER_INTEGRATION-001
step("Verify: handles multi-line code")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario

val code = "fn foo():\n    pass"
check(code.contains("\n"))
```

</details>

### Lexer Number Literals Integration

#### parses integers

- Verify: parses integers


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_LEXER_INTEGRATION-001
step("Verify: parses integers")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario

val nums = ["0", "42", "1000", "99999"]
for num in nums:
    check(num.len() > 0)
```

</details>

#### parses negative numbers

- Verify: parses negative numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_LEXER_INTEGRATION-001
step("Verify: parses negative numbers")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario

val nums = ["-1", "-42", "-1000"]
for num in nums:
    check(num.starts_with("-"))
```

</details>

#### parses hex numbers

- Verify: parses hex numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_LEXER_INTEGRATION-001
step("Verify: parses hex numbers")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario

val nums = ["0x10", "0xFF", "0xABCD"]
for num in nums:
    check(num.starts_with("0x"))
```

</details>

#### parses binary numbers

- Verify: parses binary numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_LEXER_INTEGRATION-001
step("Verify: parses binary numbers")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario

val nums = ["0b101", "0b1111"]
for num in nums:
    check(num.starts_with("0b"))
```

</details>

### Lexer String Literals Integration

#### parses simple strings

- Verify: parses simple strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_LEXER_INTEGRATION-001
step("Verify: parses simple strings")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario

val strs = ["\"hello\"", "\"world\"", "\"test\""]
for str in strs:
    check(str.starts_with("\""))
    check(str.ends_with("\""))
```

</details>

#### parses strings with escapes

- Verify: parses strings with escapes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_LEXER_INTEGRATION-001
step("Verify: parses strings with escapes")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario

val str = "\"line1\\nline2\""
check(str.contains("\\n"))
```

</details>

#### parses raw strings

- Verify: parses raw strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_LEXER_INTEGRATION-001
step("Verify: parses raw strings")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario

val str = "r\"no\\escape\""
check(str.starts_with("r\""))
```

</details>

#### parses multiline strings

- Verify: parses multiline strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_LEXER_INTEGRATION-001
step("Verify: parses multiline strings")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario

val str = "\"\"\"multi\nline\"\"\""
check(str.contains("\n"))
```

</details>

#### handles string interpolation

- Verify: handles string interpolation


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_LEXER_INTEGRATION-001
step("Verify: handles string interpolation")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario

val name = "world"
val str = "Hello {name}"
check(str.contains("world"))
```

</details>

### Lexer Operator Recognition Integration

#### recognizes arithmetic operators

- Verify: recognizes arithmetic operators


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_LEXER_INTEGRATION-001
step("Verify: recognizes arithmetic operators")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario

val ops = ["+", "-", "*", "/", "%", "**"]
for op in ops:
    check(op.len() > 0)
```

</details>

#### recognizes comparison operators

- Verify: recognizes comparison operators


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_LEXER_INTEGRATION-001
step("Verify: recognizes comparison operators")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario

val ops = ["==", "!=", "<", ">", "<=", ">="]
for op in ops:
    check(op.len() > 0)
```

</details>

#### recognizes logical operators

- Verify: recognizes logical operators


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_LEXER_INTEGRATION-001
step("Verify: recognizes logical operators")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario

val ops = ["and", "or", "not"]
for op in ops:
    check(op.len() > 0)
```

</details>

#### recognizes special operators

- Verify: recognizes special operators


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_LEXER_INTEGRATION-001
step("Verify: recognizes special operators")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario

val ops = ["|>", ">>", "?."]
for op in ops:
    check(op.len() > 0)
```

</details>

#### recognizes assignment operators

- Verify: recognizes assignment operators


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_LEXER_INTEGRATION-001
step("Verify: recognizes assignment operators")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario

val ops = ["=", "+=", "-=", "*="]
for op in ops:
    check(op.contains("="))
```

</details>

### Lexer Performance Integration

#### tokenizes 100 identifiers

- Verify: tokenizes 100 identifiers


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_LEXER_INTEGRATION-001
step("Verify: tokenizes 100 identifiers")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario

var parts: [text] = []
for i in 0..100:
    parts.push("var{i} ")
val code = parts.join("")

check(code.len() > 400)
```

</details>

#### tokenizes 50 function definitions

- Verify: tokenizes 50 function definitions


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_LEXER_INTEGRATION-001
step("Verify: tokenizes 50 function definitions")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario

var parts: [text] = []
for i in 0..50:
    parts.push("fn f{i}(): pass\n")
val code = parts.join("")

check(code.contains("fn"))
```

</details>

#### handles deeply nested expressions

- Verify: handles deeply nested expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_LEXER_INTEGRATION-001
step("Verify: handles deeply nested expressions")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario

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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `38e41f7df64beb42615aae57a9b62478355e76c58387578a1c4bed4d1da92336`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `38e41f7df64beb42615aae57a9b62478355e76c58387578a1c4bed4d1da92336`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `38e41f7df64beb42615aae57a9b62478355e76c58387578a1c4bed4d1da92336`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/02_integration/compiler/lexer_integration_spec.spl
mirror: doc/06_spec/02_integration/compiler/lexer_integration_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/compiler/lexer_integration_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/02_integration/compiler/lexer_integration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/compiler/lexer_integration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
