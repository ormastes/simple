# Protocol Types Specification

> Tests covering Position Type, Range Type, DiagnosticSeverity Enum, Diagnostic Type, Protocol Type Integration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Protocol Types Specification

## Scenarios

### Position Type

#### creates position with line and character

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates position with line and character


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates position with line and character")
val pos = Position { line: 10, character: 5 }
expect pos.line == 10
expect pos.character == 5
```

</details>

#### handles zero-based positions

- handles zero-based positions


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles zero-based positions")
val origin = Position { line: 0, character: 0 }
expect origin.line == 0
expect origin.character == 0
```

</details>

#### handles large line numbers

- handles large line numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles large line numbers")
val large_pos = Position { line: 10000, character: 100 }
expect large_pos.line == 10000
expect large_pos.character == 100
```

</details>

#### compares positions

- compares positions


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares positions")
val pos1 = Position { line: 5, character: 10 }
val pos2 = Position { line: 5, character: 10 }
val pos3 = Position { line: 5, character: 15 }

expect pos1.line == pos2.line
expect pos1.character == pos2.character
expect pos3.character != pos1.character
```

</details>

### Range Type

#### creates range from two positions

- creates range from two positions


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates range from two positions")
val start = Position { line: 0, character: 0 }
val end = Position { line: 0, character: 10 }
val range = Range { start: start, end: end }

expect range.start.line == 0
expect range.end.character == 10
```

</details>

#### handles single-line ranges

- handles single-line ranges


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles single-line ranges")
val start = Position { line: 5, character: 0 }
val end = Position { line: 5, character: 20 }
val range = Range { start: start, end: end }

expect range.start.line == range.end.line
```

</details>

#### handles multi-line ranges

- handles multi-line ranges


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles multi-line ranges")
val start = Position { line: 5, character: 0 }
val end = Position { line: 10, character: 20 }
val range = Range { start: start, end: end }

expect range.start.line < range.end.line
```

</details>

#### calculates range length for single line

- calculates range length for single line


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calculates range length for single line")
val start = Position { line: 0, character: 5 }
val end = Position { line: 0, character: 15 }
val range = Range { start: start, end: end }

val length = end.character - start.character
expect length == 10
```

</details>

### DiagnosticSeverity Enum

#### has Error severity

- has Error severity


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has Error severity")
val severity = DiagnosticSeverity.Error
match severity:
    case DiagnosticSeverity.Error:
        expect true
    _ =>
        fail "Should be Error"
```

</details>

#### has Warning severity

- has Warning severity


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has Warning severity")
val severity = DiagnosticSeverity.Warning
match severity:
    case DiagnosticSeverity.Warning:
        expect true
    _ =>
        fail "Should be Warning"
```

</details>

#### has Information severity

- has Information severity


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has Information severity")
val severity = DiagnosticSeverity.Information
match severity:
    case DiagnosticSeverity.Information:
        expect true
    _ =>
        fail "Should be Information"
```

</details>

#### has Hint severity

- has Hint severity


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has Hint severity")
val severity = DiagnosticSeverity.Hint
match severity:
    case DiagnosticSeverity.Hint:
        expect true
    _ =>
        fail "Should be Hint"
```

</details>

#### distinguishes between severities

- distinguishes between severities


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("distinguishes between severities")
val error = DiagnosticSeverity.Error
val warning = DiagnosticSeverity.Warning

match error:
    case DiagnosticSeverity.Error:
        expect true
    case DiagnosticSeverity.Warning:
        fail "Should be Error, not Warning"
    _ =>
        fail "Unexpected severity"
```

</details>

### Diagnostic Type

#### creates diagnostic with all fields

- creates diagnostic with all fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates diagnostic with all fields")
val range = Range {
    start: Position { line: 0, character: 0 },
    end: Position { line: 0, character: 5 }
}
val diag = Diagnostic {
    range: range,
    severity: DiagnosticSeverity.Error,
    message: "Undefined variable",
    source: "simple-compiler"
}

expect diag.message == "Undefined variable"
expect diag.source == "simple-compiler"
```

</details>

#### creates error diagnostic

- creates error diagnostic


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates error diagnostic")
val range = Range {
    start: Position { line: 5, character: 10 },
    end: Position { line: 5, character: 15 }
}
val error = Diagnostic {
    range: range,
    severity: DiagnosticSeverity.Error,
    message: "Syntax error",
    source: "parser"
}

match error.severity:
    case DiagnosticSeverity.Error:
        expect true
    _ =>
        fail "Should be Error severity"
```

</details>

#### creates warning diagnostic

- creates warning diagnostic


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates warning diagnostic")
val range = Range {
    start: Position { line: 10, character: 0 },
    end: Position { line: 10, character: 20 }
}
val warning = Diagnostic {
    range: range,
    severity: DiagnosticSeverity.Warning,
    message: "Unused variable",
    source: "linter"
}

match warning.severity:
    case DiagnosticSeverity.Warning:
        expect true
    _ =>
        fail "Should be Warning severity"
```

</details>

#### stores diagnostic message

- stores diagnostic message


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores diagnostic message")
val range = Range {
    start: Position { line: 0, character: 0 },
    end: Position { line: 0, character: 1 }
}
val diag = Diagnostic {
    range: range,
    severity: DiagnosticSeverity.Information,
    message: "Consider using const",
    source: "advisor"
}

expect diag.message.len() > 0
expect diag.message.contains("const")
```

</details>

### Protocol Type Integration

#### builds diagnostic with position and range

- builds diagnostic with position and range


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds diagnostic with position and range")
val pos_start = Position { line: 5, character: 0 }
val pos_end = Position { line: 5, character: 10 }
val range = Range { start: pos_start, end: pos_end }
val diagnostic = Diagnostic {
    range: range,
    severity: DiagnosticSeverity.Error,
    message: "Type mismatch",
    source: "type-checker"
}

expect diagnostic.range.start.line == 5
expect diagnostic.range.end.character == 10
expect diagnostic.message == "Type mismatch"
```

</details>

#### creates multiple diagnostics for same range

- creates multiple diagnostics for same range


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates multiple diagnostics for same range")
val range = Range {
    start: Position { line: 10, character: 5 },
    end: Position { line: 10, character: 15 }
}

val error = Diagnostic {
    range: range,
    severity: DiagnosticSeverity.Error,
    message: "Error 1",
    source: "source1"
}

val warning = Diagnostic {
    range: range,
    severity: DiagnosticSeverity.Warning,
    message: "Warning 1",
    source: "source2"
}

expect error.range.start.line == warning.range.start.line
expect error.severity != warning.severity
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/lsp/protocol_types_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Position Type, Range Type, DiagnosticSeverity Enum, Diagnostic Type, Protocol Type Integration.
- Position Type
- Range Type
- DiagnosticSeverity Enum
- Diagnostic Type
- Protocol Type Integration

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

- Canonical SPipe generation for source `b06c87680d4d4c5d294f931e448ab38587b617a74eee42037355e31aed7fb8b7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b06c87680d4d4c5d294f931e448ab38587b617a74eee42037355e31aed7fb8b7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b06c87680d4d4c5d294f931e448ab38587b617a74eee42037355e31aed7fb8b7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/lsp/protocol_types_spec.spl
mirror: doc/06_spec/unit/app/lsp/protocol_types_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/lsp/protocol_types_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/lsp/protocol_types_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/lsp/protocol_types_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates position with line and character' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/lsp/protocol_types_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles zero-based positions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/lsp/protocol_types_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles large line numbers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
