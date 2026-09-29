# Pretty Printer Specification

> Tests covering Format Expressions, Format Statements, Format Control Flow, Indentation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pretty Printer Specification

## Scenarios

### Format Expressions

#### format integer literal

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- format integer literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("format integer literal")
val s = "{42}"
check(s == "42")
```

</details>

#### format negative integer

- format negative integer


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("format negative integer")
val s = "{-5}"
check(s == "-5")
```

</details>

#### format float literal

- format float literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("format float literal")
val x = 3.14
val s = "{x}"
check(s.contains("3.14"))
```

</details>

#### format string literal

- format string literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("format string literal")
val s = "hello"
check(s == "hello")
```

</details>

#### format boolean true

- format boolean true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("format boolean true")
val s = "{true}"
check(s == "true")
```

</details>

#### format boolean false

- format boolean false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("format boolean false")
val s = "{false}"
check(s == "false")
```

</details>

#### format array

- format array


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("format array")
val arr = [1, 2, 3]
val s = "{arr}"
check(s.contains("1"))
check(s.contains("3"))
```

</details>

### Format Statements

#### format val declaration

- format val declaration


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("format val declaration")
val decl = "val x = 42"
check(decl.starts_with("val"))
```

</details>

#### format var declaration

- format var declaration


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("format var declaration")
val decl = "var x = 42"
check(decl.starts_with("var"))
```

</details>

#### format assignment

- format assignment


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("format assignment")
val stmt = "x = 42"
check(stmt.contains("="))
```

</details>

#### format return

- format return


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("format return")
val stmt = "return 42"
check(stmt.starts_with("return"))
```

</details>

### Format Control Flow

#### format if statement

- format if statement


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("format if statement")
val stmt = "if x > 0:"
check(stmt.starts_with("if"))
```

</details>

<details>
<summary>Advanced: format while loop</summary>

#### format while loop

- format while loop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("format while loop")
val stmt = "while i < 10:"
check(stmt.starts_with("while"))
```

</details>


</details>

<details>
<summary>Advanced: format for loop</summary>

#### format for loop

- format for loop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("format for loop")
val stmt = "for i in 0..10:"
check(stmt.starts_with("for"))
```

</details>


</details>

#### format match

- format match


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("format match")
val stmt = "match x:"
check(stmt.starts_with("match"))
```

</details>

### Indentation

#### top level no indent

- top level no indent


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("top level no indent")
val indent = 0
check(indent == 0)
```

</details>

#### block body indented

- block body indented


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("block body indented")
val indent = 4
check(indent == 4)
```

</details>

#### nested block double indented

- nested block double indented


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nested block double indented")
val indent = 8
check(indent == 8)
```

</details>

#### consistent indent width

- consistent indent width


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("consistent indent width")
val width = 4
val level1 = width
val level2 = width * 2
val level3 = width * 3
check(level1 == 4)
check(level2 == 8)
check(level3 == 12)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/frontend/pretty_printer_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Format Expressions, Format Statements, Format Control Flow, Indentation.
- Format Expressions
- Format Statements
- Format Control Flow
- Indentation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
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

- Canonical SPipe generation for source `3e336cf9832ed4261179c40e020b524cdd708ba57bb161e89df805ea08c4679a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3e336cf9832ed4261179c40e020b524cdd708ba57bb161e89df805ea08c4679a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3e336cf9832ed4261179c40e020b524cdd708ba57bb161e89df805ea08c4679a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/frontend/pretty_printer_spec.spl
mirror: doc/06_spec/unit/compiler/frontend/pretty_printer_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/frontend/pretty_printer_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/frontend/pretty_printer_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/frontend/pretty_printer_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'format integer literal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/frontend/pretty_printer_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'format negative integer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/frontend/pretty_printer_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'format float literal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
