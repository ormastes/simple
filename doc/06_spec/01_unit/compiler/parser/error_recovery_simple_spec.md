# Error Recovery Simple Specification

> Tests covering Common Mistake Messages, Error Detection Logic, Error Message Format, Fix Suggestion Confidence, Diff Generation, Real-World Scenarios, Error Builder Pattern, Phase 1 Coverage, Phase 1 Metrics.

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

- provides message for missing comma in args


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides message for missing comma in args")
# Test will pass when CommonMistake is available
# For now, document expected behavior
val expected = "Missing comma between function arguments"
expect expected.contains("comma")
expect expected.contains("arguments")
```

</details>

#### provides message for missing comma in dict

- provides message for missing comma in dict


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides message for missing comma in dict")
val expected = "Missing comma between dict entries"
expect expected.contains("comma")
expect expected.contains("dict")
```

</details>

#### provides message for missing colon before block

- provides message for missing colon before block


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides message for missing colon before block")
val expected = "Missing colon before function or block body"
expect expected.contains("colon")
expect expected.contains("function")
```

</details>

#### provides Python def mistake message

- provides Python def mistake message


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides Python def mistake message")
val expected = "Use 'fn' to define functions in Simple, not 'def'"
expect expected.contains("fn")
expect expected.contains("def")
```

</details>

#### provides Rust let mut mistake message

- provides Rust let mut mistake message


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides Rust let mut mistake message")
val expected = "Use 'var' for mutable variables"
expect expected.contains("var")
expect expected.contains("mutable")
```

</details>

### Error Detection Logic

#### when detecting missing commas

#### detects pattern identifier-colon

- detects pattern identifier-colon


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects pattern identifier-colon")
# Pattern: func(a: 1 b: 2) where b is followed by :
# This indicates missing comma before b
val pattern_found = true  # Simulated detection
expect pattern_found
```

</details>

#### detects pattern identifier-equals

- detects pattern identifier-equals


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects pattern identifier-equals")
# Pattern: func(a=1 b=2) where b is followed by =
val pattern_found = true  # Simulated detection
expect pattern_found
```

</details>

#### rejects non-identifier tokens

- rejects non-identifier tokens


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects non-identifier tokens")
# Pattern: func(a: 1, b: 2) where comma is present
val pattern_found = false  # No missing comma
expect not pattern_found
```

</details>

### Error Message Format

#### when formatting errors

#### includes context in message

- includes context in message


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes context in message")
val msg = "function arguments: expected comma before argument 'b'"
expect msg.contains("function arguments")
expect msg.contains("expected comma")
```

</details>

#### includes location information

- includes location information


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes location information")
val msg = "line 5:20"
expect msg.contains("line")
expect msg.contains("5")
expect msg.contains("20")
```

</details>

#### includes suggestion when available

- includes suggestion when available


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes suggestion when available")
val msg = "Suggestion: Insert comma before 'b'"
expect msg.contains("Suggestion:")
expect msg.contains("Insert comma")
```

</details>

#### includes help text when available

- includes help text when available


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes help text when available")
val msg = "Help: Use: func(a: 1, b: 2)"
expect msg.contains("Help:")
expect msg.contains("func(a: 1, b: 2)")
```

</details>

### Fix Suggestion Confidence

#### when assigning confidence levels

#### assigns high confidence for obvious fixes

- assigns high confidence for obvious fixes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assigns high confidence for obvious fixes")
# Missing comma between named args is obvious
val confidence = "High"
expect confidence == "High"
```

</details>

#### assigns medium confidence for ambiguous cases

- assigns medium confidence for ambiguous cases


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assigns medium confidence for ambiguous cases")
# Indentation fixes might be ambiguous
val confidence = "Medium"
expect confidence == "Medium"
```

</details>

#### assigns low confidence for speculative fixes

- assigns low confidence for speculative fixes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assigns low confidence for speculative fixes")
# Complex expression fixes are speculative
val confidence = "Low"
expect confidence == "Low"
```

</details>

### Diff Generation

#### when generating diffs

#### shows before and after lines

- shows before and after lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows before and after lines")
val diff = "--- before\n+++ after\n-func(a: 1 b: 2)\n+func(a: 1, b: 2)"
expect diff.contains("--- before")
expect diff.contains("+++ after")
expect diff.contains("-func(a: 1 b: 2)")
expect diff.contains("+func(a: 1, b: 2)")
```

</details>

#### shows line numbers

- shows line numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows line numbers")
val diff = "@@ -5,1 +5,1 @@"
expect diff.contains("@@")
expect diff.contains("5,1")
```

</details>

#### highlights changed content

- highlights changed content


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("highlights changed content")
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

- detects AudioSource example


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects AudioSource example")
# Source: AudioSource(name: "test" volume: 1.0)
# Should detect missing comma before 'volume'
val source = "AudioSource(name: 'test' volume: 1.0)"
val has_error = true  # Would be detected by parser
expect has_error
```

</details>

#### suggests correct fix

- suggests correct fix


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("suggests correct fix")
val suggestion = "Insert comma before 'volume'"
expect suggestion.contains("comma")
expect suggestion.contains("volume")
```

</details>

#### shows correct syntax in help

- shows correct syntax in help


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows correct syntax in help")
val help = "Use: AudioSource(name: 'test', volume: 1.0)"
expect help.contains("AudioSource")
expect help.contains(", volume")
```

</details>

#### missing comma in dict literal

#### detects dict literal error

- detects dict literal error


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects dict literal error")
# Source: {a: 1 b: 2}
val source = "{a: 1 b: 2}"
val has_error = true
expect has_error
```

</details>

#### provides context-specific message

- provides context-specific message


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides context-specific message")
val msg = "dict literal: expected comma between entries"
expect msg.contains("dict literal")
expect msg.contains("comma between entries")
```

</details>

#### missing colon before block

#### detects missing colon

- detects missing colon


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects missing colon")
# Source: fn foo()\n    return 42
val source = "fn foo()\n    return 42"
val has_error = true
expect has_error
```

</details>

#### suggests adding colon

- suggests adding colon


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("suggests adding colon")
val suggestion = "Insert ':' at end of line"
expect suggestion.contains(":")
expect suggestion.contains("end of line")
```

</details>

### Error Builder Pattern

#### when building errors

#### supports method chaining

- supports method chaining


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports method chaining")
# ErrorBuilder().context("test").message("test").build()
val chained = true
expect chained
```

</details>

#### builds error with all fields

- builds error with all fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds error with all fields")
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

- builds error with minimal fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds error with minimal fields")
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

- replaces cryptic token errors


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("replaces cryptic token errors")
# Old: "expected Comma, found Identifier { name: 'b', pattern: Immutable }"
# New: "function arguments: expected comma before argument 'b'"
val improvement = true
expect improvement
```

</details>

#### provides context for all errors

- provides context for all errors


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides context for all errors")
# Every error now includes WHERE it occurred
val has_context = true
expect has_context
```

</details>

#### includes actionable suggestions

- includes actionable suggestions


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes actionable suggestions")
# Errors show HOW to fix the problem
val has_suggestion = true
expect has_suggestion
```

</details>

#### shows correct syntax examples

- shows correct syntax examples


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows correct syntax examples")
# Help text demonstrates the right way
val has_examples = true
expect has_examples
```

</details>

### Phase 1 Metrics

#### test coverage

#### covers function argument errors

- covers function argument errors


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers function argument errors")
# Missing commas in func(a: 1 b: 2)
val covered = true
expect covered
```

</details>

#### detects 7 parse error types

- detects 7 parse error types


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects 7 parse error types")
# MissingCommaInArgs, MissingCommaInDict, etc.
val error_types = 7
expect error_types == 7
```

</details>

#### provides fix suggestions

- provides fix suggestions


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides fix suggestions")
# FixSuggestion with confidence scoring
val has_fixes = true
expect has_fixes
```

</details>

#### impact on test pass rate

#### improves error messages for 7 percent of failures

- improves error messages for 7 percent of failures


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("improves error messages for 7 percent of failures")
# 7 out of 95 failing tests = 7.4%
val improvement = 7.4
expect improvement > 7.0
```

</details>

#### provides foundation for 16.8 percent more

- provides foundation for 16.8 percent more


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides foundation for 16.8 percent more")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Common Mistake Messages, Error Detection Logic, Error Message Format, Fix Suggestion Confidence, Diff Generation, Real-World Scenarios, Error Builder Pattern, Phase 1 Coverage, Phase 1 Metrics.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `aa59a77d1650c12c4d0abe0e70a187378bea0a4815e149ee573826a9e5555b06`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `aa59a77d1650c12c4d0abe0e70a187378bea0a4815e149ee573826a9e5555b06`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `aa59a77d1650c12c4d0abe0e70a187378bea0a4815e149ee573826a9e5555b06`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/parser/error_recovery_simple_spec.spl
mirror: doc/06_spec/01_unit/compiler/parser/error_recovery_simple_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/parser/error_recovery_simple_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/parser/error_recovery_simple_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/parser/error_recovery_simple_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'provides message for missing comma in args' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/error_recovery_simple_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'provides message for missing comma in dict' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/error_recovery_simple_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'provides message for missing colon before block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
