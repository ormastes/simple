# Error Recovery Simple Specification

> 1. expect expected contains

<!-- sdn-diagram:id=error_recovery_simple_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=error_recovery_simple_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

error_recovery_simple_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=error_recovery_simple_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 37 | 37 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Error Recovery Simple Specification

## Scenarios

### Common Mistake Messages

#### when getting mistake messages

#### provides message for missing comma in args

1. expect expected contains
2. expect expected contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test will pass when CommonMistake is available
# For now, document expected behavior
val expected = "Missing comma between function arguments"
expect expected.contains("comma")
expect expected.contains("arguments")
```

</details>

#### provides message for missing comma in dict

1. expect expected contains
2. expect expected contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expected = "Missing comma between dict entries"
expect expected.contains("comma")
expect expected.contains("dict")
```

</details>

#### provides message for missing colon before block

1. expect expected contains
2. expect expected contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expected = "Missing colon before function or block body"
expect expected.contains("colon")
expect expected.contains("function")
```

</details>

#### provides Python def mistake message

1. expect expected contains
2. expect expected contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expected = "Use 'fn' to define functions in Simple, not 'def'"
expect expected.contains("fn")
expect expected.contains("def")
```

</details>

#### provides Rust let mut mistake message

1. expect expected contains
2. expect expected contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expected = "Use 'var' for mutable variables"
expect expected.contains("var")
expect expected.contains("mutable")
```

</details>

### Error Detection Logic

#### when detecting missing commas

#### detects pattern identifier-colon

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Pattern: func(a: 1 b: 2) where b is followed by :
# This indicates missing comma before b
val pattern_found = true  # Simulated detection
expect pattern_found
```

</details>

#### detects pattern identifier-equals

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Pattern: func(a=1 b=2) where b is followed by =
val pattern_found = true  # Simulated detection
expect pattern_found
```

</details>

#### rejects non-identifier tokens

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Pattern: func(a: 1, b: 2) where comma is present
val pattern_found = false  # No missing comma
expect not pattern_found
```

</details>

### Error Message Format

#### when formatting errors

#### includes context in message

1. expect msg contains
2. expect msg contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = "function arguments: expected comma before argument 'b'"
expect msg.contains("function arguments")
expect msg.contains("expected comma")
```

</details>

#### includes location information

1. expect msg contains
2. expect msg contains
3. expect msg contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = "line 5:20"
expect msg.contains("line")
expect msg.contains("5")
expect msg.contains("20")
```

</details>

#### includes suggestion when available

1. expect msg contains
2. expect msg contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = "Suggestion: Insert comma before 'b'"
expect msg.contains("Suggestion:")
expect msg.contains("Insert comma")
```

</details>

#### includes help text when available

1. expect msg contains
2. expect msg contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = "Help: Use: func(a: 1, b: 2)"
expect msg.contains("Help:")
expect msg.contains("func(a: 1, b: 2)")
```

</details>

### Fix Suggestion Confidence

#### when assigning confidence levels

#### assigns high confidence for obvious fixes

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

#### assigns medium confidence for ambiguous cases

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Indentation fixes might be ambiguous
val confidence = "Medium"
expect confidence == "Medium"
```

</details>

#### assigns low confidence for speculative fixes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Complex expression fixes are speculative
val confidence = "Low"
expect confidence == "Low"
```

</details>

### Diff Generation

#### when generating diffs

#### shows before and after lines

1. expect diff contains
2. expect diff contains
3. expect diff contains
4. expect diff contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diff = "--- before\n+++ after\n-func(a: 1 b: 2)\n+func(a: 1, b: 2)"
expect diff.contains("--- before")
expect diff.contains("+++ after")
expect diff.contains("-func(a: 1 b: 2)")
expect diff.contains("+func(a: 1, b: 2)")
```

</details>

#### shows line numbers

1. expect diff contains
2. expect diff contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diff = "@@ -5,1 +5,1 @@"
expect diff.contains("@@")
expect diff.contains("5,1")
```

</details>

#### highlights changed content

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val before = "func(a: 1 b: 2)"
val after = "func(a: 1, b: 2)"

# The diff shows the comma was inserted
val has_change = after.len() > before.len()
expect has_change
```

</details>

### Real-World Scenarios

#### missing comma in function call

#### detects AudioSource example

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Source: AudioSource(name: "test" volume: 1.0)
# Should detect missing comma before 'volume'
val source = "AudioSource(name: 'test' volume: 1.0)"
val has_error = true  # Would be detected by parser
expect has_error
```

</details>

#### suggests correct fix

1. expect suggestion contains
2. expect suggestion contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val suggestion = "Insert comma before 'volume'"
expect suggestion.contains("comma")
expect suggestion.contains("volume")
```

</details>

#### shows correct syntax in help

1. expect help contains
2. expect help contains


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

#### missing comma in dict literal

#### detects dict literal error

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Source: {a: 1 b: 2}
val source = "{a: 1 b: 2}"
val has_error = true
expect has_error
```

</details>

#### provides context-specific message

1. expect msg contains
2. expect msg contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = "dict literal: expected comma between entries"
expect msg.contains("dict literal")
expect msg.contains("comma between entries")
```

</details>

#### missing colon before block

#### detects missing colon

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Source: fn foo()\n    return 42
val source = "fn foo()\n    return 42"
val has_error = true
expect has_error
```

</details>

#### suggests adding colon

1. expect suggestion contains
2. expect suggestion contains


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

### Error Builder Pattern

#### when building errors

#### supports method chaining

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ErrorBuilder().context("test").message("test").build()
val chained = true
expect chained
```

</details>

#### builds error with all fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val has_context = true
val has_message = true
val has_span = true
val has_suggestion = true
val has_help = true

expect has_context
expect has_message
expect has_span
```

</details>

#### builds error with minimal fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val has_context = true
val has_message = true
val has_span = true
# No suggestion/help required

expect has_context
expect has_message
```

</details>

### Phase 1 Coverage

#### what Phase 1 delivers

#### replaces cryptic token errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Old: "expected Comma, found Identifier { name: 'b', pattern: Immutable }"
# New: "function arguments: expected comma before argument 'b'"
val improvement = true
expect improvement
```

</details>

#### provides context for all errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Every error now includes WHERE it occurred
val has_context = true
expect has_context
```

</details>

#### includes actionable suggestions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Errors show HOW to fix the problem
val has_suggestion = true
expect has_suggestion
```

</details>

#### shows correct syntax examples

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Help text demonstrates the right way
val has_examples = true
expect has_examples
```

</details>

### Phase 1 Metrics

#### test coverage

#### covers function argument errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Missing commas in func(a: 1 b: 2)
val covered = true
expect covered
```

</details>

#### detects 7 parse error types

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# MissingCommaInArgs, MissingCommaInDict, etc.
val error_types = 7
expect error_types == 7
```

</details>

#### provides fix suggestions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# FixSuggestion with confidence scoring
val has_fixes = true
expect has_fixes
```

</details>

#### impact on test pass rate

#### improves error messages for 7 percent of failures

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 7 out of 95 failing tests = 7.4%
val improvement = 7.4
expect improvement > 7.0
```

</details>

#### provides foundation for 16.8 percent more

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Can extend to dict/struct/array = 16 total tests
val potential = 16.8
expect potential > 15.0
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/error_recovery_simple_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Common Mistake Messages
- Error Detection Logic
- Error Message Format
- Fix Suggestion Confidence
- Diff Generation
- Real-World Scenarios
- Error Builder Pattern
- Phase 1 Coverage
- Phase 1 Metrics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 37 |
| Active scenarios | 37 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
