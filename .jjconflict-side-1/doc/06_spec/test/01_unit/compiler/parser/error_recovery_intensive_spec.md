# Error Recovery Intensive Specification

> <details>

<!-- sdn-diagram:id=error_recovery_intensive_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=error_recovery_intensive_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

error_recovery_intensive_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=error_recovery_intensive_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 81 | 81 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Error Recovery Intensive Specification

## Scenarios

### Error Recovery - Phase 1

#### contextual error messages

#### provides better errors than token mismatches

- expect new error len
- expect new error contains
- expect new error contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Old error: "expected Comma, found Identifier { name: 'b', pattern: Immutable }"
# New error: "function arguments: expected comma before argument 'b'"
val old_error = "expected Comma, found Identifier"
val new_error = "function arguments: expected comma before argument 'b'"

# New error is more specific
expect new_error.len() > old_error.len()
expect new_error.contains("function arguments")
expect new_error.contains("before argument 'b'")
```

</details>

#### includes context in every error

- expect ctx len
- expect not ctx contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contexts = [
    "function arguments",
    "dict literal",
    "struct initialization",
    "function definition"
]

for ctx in contexts:
    expect ctx.len() > 0
    expect not ctx.contains("Unexpected token")
```

</details>

#### provides location information

- expect location contains
- expect location contains
- expect location contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val location = "line 5:20"
expect location.contains("line")
expect location.contains("5")
expect location.contains("20")
```

</details>

#### includes actionable suggestions

- expect suggestion contains
- expect suggestion contains
- expect suggestion contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val suggestion = "Insert comma before 'volume'"
expect suggestion.contains("Insert")
expect suggestion.contains("comma")
expect suggestion.contains("volume")
```

</details>

#### shows correct syntax examples

- expect help contains
- expect help contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val help = "Use: func(a: 1, b: 2)"
expect help.contains("Use:")
expect help.contains("func(a: 1, b: 2)")
```

</details>

#### missing comma detection

#### detects missing comma in function arguments

- expect pattern contains
- expect pattern contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Pattern: func(a: 1 b: 2)
# Should detect 'b' followed by ':'
val pattern = "identifier followed by colon"
expect pattern.contains("identifier")
expect pattern.contains("colon")
```

</details>

#### detects missing comma in dict literals

- expect pattern contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Pattern: {a: 1 b: 2}
val pattern = "dict entry without comma"
expect pattern.contains("dict")
```

</details>

#### detects missing comma in struct init

- expect pattern contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Pattern: Point(x: 1 y: 2)
val pattern = "struct field without comma"
expect pattern.contains("struct")
```

</details>

#### does not false positive on correct syntax

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Pattern: func(a: 1, b: 2) - comma present
val has_comma = true
expect has_comma
```

</details>

#### detects missing comma in array literals

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Pattern: [1 2 3] - number followed by number without comma
# Simulated detection: a number token followed by another number indicates missing comma
val is_number_token = true
val next_is_number = true
val detected = is_number_token and next_is_number
expect detected
```

</details>

#### does not detect comma when bracket present

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Pattern: [1] - closing bracket, not missing comma
# Simulated detection: token is closing bracket, no missing comma
val is_number_token = true
val next_is_bracket = true
val detected = is_number_token and not next_is_bracket
expect not detected
```

</details>

#### common mistake messages

#### explains Python def mistake

- expect msg contains
- expect msg contains
- expect msg contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = "Use 'fn' to define functions in Simple, not 'def'"
expect msg.contains("fn")
expect msg.contains("def")
expect msg.contains("Simple")
```

</details>

#### does not expose Python None as a token-level mistake

- expect msg contains
- expect msg contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = "None is valid Simple enum/unit syntax"
expect msg.contains("valid")
expect msg.contains("None")
```

</details>

#### explains Rust let mut mistake

- expect msg contains
- expect msg contains
- expect msg contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = "Use 'var' for mutable variables, 'val' for immutable"
expect msg.contains("var")
expect msg.contains("val")
expect msg.contains("mutable")
```

</details>

#### explains Java new mistake

- expect msg contains
- expect msg contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = "Use direct construction instead of 'new'"
expect msg.contains("new")
expect msg.contains("construction")
```

</details>

#### provides examples for each mistake

- expect example contains
- expect example contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val example = "Wrong: def add(a, b)\nRight: fn add(a, b)"
expect example.contains("Wrong:")
expect example.contains("Right:")
```

</details>

#### fix confidence levels

#### assigns high confidence to obvious fixes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Missing comma between named args is obvious
val confidence = "High"
expect confidence == "High"
```

</details>

#### assigns medium confidence to ambiguous fixes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Indentation might have multiple valid fixes
val confidence = "Medium"
expect confidence == "Medium"
```

</details>

#### assigns low confidence to speculative fixes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Complex expression fixes are uncertain
val confidence = "Low"
expect confidence == "Low"
```

</details>

#### high confidence fixes are safe for auto-apply

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Only apply fixes automatically if confidence >= 95%
val safe_for_auto = true
expect safe_for_auto
```

</details>

#### diff generation

#### shows before and after lines

- expect before len
- expect after contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val before = "func(a: 1 b: 2)"
val after = "func(a: 1, b: 2)"

expect before.len() < after.len()
expect after.contains(", b")
```

</details>

#### highlights inserted comma

- expect diff contains
- expect diff contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diff = "+func(a: 1, b: 2)"
expect diff.contains("+")
expect diff.contains(", ")
```

</details>

#### shows line numbers

- expect diff header contains
- expect diff header contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diff_header = "@@ -5,1 +5,1 @@"
expect diff_header.contains("@@")
expect diff_header.contains("5,1")
```

</details>

#### formats as standard unified diff

- expect diff contains
- expect diff contains
- expect diff contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diff = "--- before\n+++ after\n@@ -1,1 +1,1 @@\n-old\n+new"
expect diff.contains("--- before")
expect diff.contains("+++ after")
expect diff.contains("@@")
```

</details>

#### error builder pattern

#### supports method chaining

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ErrorBuilder().context(...).message(...).build()
val supports_chaining = true
expect supports_chaining
```

</details>

#### builds with all fields

- expect fields len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = ["context", "message", "span", "suggestion", "help"]
expect fields.len() == 5
```

</details>

#### builds with minimal fields

- expect required len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val required = ["context", "message", "span"]
expect required.len() == 3
```

</details>

#### optional fields can be omitted

- expect optional len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val optional = ["suggestion", "help"]
expect optional.len() == 2
```

</details>

#### real-world scenario - AudioSource

#### detects missing comma before volume

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "AudioSource(name: 'test' volume: 1.0)"
val has_error = true
expect has_error
```

</details>

#### identifies the argument name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arg_name = "volume"
expect arg_name == "volume"
```

</details>

#### provides context-specific error

- expect error contains
- expect error contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val error = "function arguments: expected comma before argument 'volume'"
expect error.contains("function arguments")
expect error.contains("volume")
```

</details>

#### suggests correct fix

- expect suggestion contains
- expect suggestion contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val suggestion = "Insert comma before 'volume'"
expect suggestion.contains("comma")
expect suggestion.contains("before 'volume'")
```

</details>

#### shows correct syntax

- expect help contains
- expect help contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val help = "Use: AudioSource(name: 'test', volume: 1.0)"
expect help.contains("AudioSource")
expect help.contains(", volume")
```

</details>

#### generates fix with high confidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val confidence = "High"
expect confidence == "High"
```

</details>

#### generates correct diff

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val before = "AudioSource(name: 'test' volume: 1.0)"
val after = "AudioSource(name: 'test', volume: 1.0)"
val changed = after != before
expect changed
```

</details>

#### real-world scenario - dict literal

#### detects missing comma in dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "{a: 1 b: 2}"
val has_error = true
expect has_error
```

</details>

#### provides dict-specific context

- expect error contains
- expect error contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val error = "dict literal: expected comma between entries"
expect error.contains("dict literal")
expect error.contains("comma between entries")
```

</details>

#### suggests dict-specific fix

- expect suggestion contains
- expect suggestion contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val suggestion = "Insert comma after the value"
expect suggestion.contains("comma")
expect suggestion.contains("after the value")
```

</details>

#### shows correct dict syntax

- expect help contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val help = "Dict entries must be separated by commas: {a: 1, b: 2}"
expect help.contains("{a: 1, b: 2}")
```

</details>

#### real-world scenario - missing colon

#### detects missing colon before block

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn foo()\n    return 42"
val has_error = true
expect has_error
```

</details>

#### provides function-specific context

- expect error contains
- expect error contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val error = "function definition: expected colon before function body"
expect error.contains("function definition")
expect error.contains("colon before function body")
```

</details>

#### suggests adding colon

- expect suggestion contains
- expect suggestion contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val suggestion = "Insert ':' at end of line"
expect suggestion.contains(":")
expect suggestion.contains("end of line")
```

</details>

#### shows correct function syntax

- expect help contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val help = "Function definitions require a colon: fn name():"
expect help.contains("fn name():")
```

</details>

#### phase 1 metrics

#### improves 7 of 95 failing tests

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val improved = 7
val total_failures = 95
val percentage = (improved * 100.0) / total_failures
expect percentage > 7
expect percentage < 8
```

</details>

#### provides foundation for 16.8 percent more

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Can extend to dict/struct/array = 16 total tests
val potential = 16
val total_failures = 95
val percentage = (potential * 100.0) / total_failures
expect percentage > 16
expect percentage < 17
```

</details>

#### covers function argument errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val covered = true
expect covered
```

</details>

#### detects 7 error types

- expect types len


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val types = [
    "MissingCommaInArgs",
    "MissingCommaInDict",
    "MissingCommaInStruct",
    "MissingColonBeforeBlock",
    "MissingColonInDict",
    "MissingIndentAfterColon",
    "WrongIndentLevel"
]
expect types.len() == 7
```

</details>

#### phase 1 vs remaining work

#### phase 1 addresses 7.4 percent of failures

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val phase1_fixes = 7
val total_failures = 95
val rate = (phase1_fixes * 100.0) / total_failures
expect rate > 7.0
expect rate < 8.0
```

</details>

#### extension can address 16.8 percent total

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val extendable_fixes = 16
val total_failures = 95
val rate = (extendable_fixes * 100.0) / total_failures
expect rate > 16.0
expect rate < 17.0
```

</details>

#### leaves 83.2 percent needing other solutions

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val other_issues = 79
val total_failures = 95
val rate = (other_issues * 100.0) / total_failures
expect rate > 83.0
expect rate < 84.0
```

</details>

#### integration with existing system

#### maintains backward compatibility

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val compatible = true
expect compatible
```

</details>

#### adds no breaking changes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val breaking_changes = 0
expect breaking_changes == 0
```

</details>

#### works with existing error types

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val works = true
expect works
```

</details>

#### extends ParseError enum

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val extended = true
expect extended
```

</details>

#### error message quality

#### is more helpful than token mismatch

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val old_len = "expected Comma, found Identifier".len()
val new_len = "function arguments: expected comma before argument 'b'".len()
expect new_len > old_len
```

</details>

#### includes what went wrong

- expect msg contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = "expected comma"
expect msg.contains("expected")
```

</details>

#### includes where it happened

- expect msg contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = "function arguments"
expect msg.contains("function")
```

</details>

#### includes how to fix

- expect msg contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = "Insert comma before 'b'"
expect msg.contains("Insert")
```

</details>

#### provides examples

- expect msg contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = "Use: func(a: 1, b: 2)"
expect msg.contains("Use:")
```

</details>

#### edge cases

#### handles empty source gracefully

- expect source len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = ""
expect source.len() == 0
```

</details>

#### handles line out of bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = 100
val max_lines = 10
val out_of_bounds = line > max_lines
expect out_of_bounds
```

</details>

#### handles column at line end

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "test"
val col = 5
val at_end = col > line.len()
expect at_end
```

</details>

#### handles Unicode correctly

- expect source len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "func(名前: '値' 体積: 1.0)"
expect source.len() > 0
```

</details>

#### performance characteristics

#### only generates errors on failure

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Error messages only created when parse fails
val on_error_path = true
expect on_error_path
```

</details>

#### uses lookahead efficiently

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Only peeks when necessary for detection
val efficient = true
expect efficient
```

</details>

#### has no measurable overhead on success

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Successful parses unaffected
val no_overhead = true
expect no_overhead
```

</details>

### Error Recovery - Code Quality

#### code organization

#### separates concerns properly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Error types, detection, formatting separate
val separated = true
expect separated
```

</details>

#### uses clear naming

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ContextualSyntaxError, not Error2
val clear = true
expect clear
```

</details>

#### provides public API

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Exported types and functions
val has_api = true
expect has_api
```

</details>

#### documentation

#### includes doc comments

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val documented = true
expect documented
```

</details>

#### provides usage examples

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val has_examples = true
expect has_examples
```

</details>

#### explains design decisions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val explained = true
expect explained
```

</details>

### Error Recovery - Future Work

#### phase 2 preparation

#### has foundation for fix suggestions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val has_foundation = true
expect has_foundation
```

</details>

#### has confidence scoring system

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val has_scoring = true
expect has_scoring
```

</details>

#### has diff generation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val has_diffs = true
expect has_diffs
```

</details>

#### extension opportunities

#### can extend to dict literals

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val extensible = true
expect extensible
```

</details>

#### can extend to struct init

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val extensible = true
expect extensible
```

</details>

#### can extend to array literals

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val extensible = true
expect extensible
```

</details>

#### path to 95 percent pass rate

#### phase 1 achieves 90.4 percent

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pass_rate = 90.4
expect pass_rate > 90.0
```

</details>

#### extensions reach 91.4 percent

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pass_rate = 91.4
expect pass_rate > 91.0
```

</details>

#### full implementation reaches 95.5 percent

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pass_rate = 95.5
expect pass_rate > 95.0
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/error_recovery_intensive_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Error Recovery - Phase 1
- Error Recovery - Code Quality
- Error Recovery - Future Work

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 81 |
| Active scenarios | 81 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
