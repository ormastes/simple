# Protocol Types Specification

> <details>

<!-- sdn-diagram:id=protocol_types_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=protocol_types_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

protocol_types_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=protocol_types_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Protocol Types Specification

## Scenarios

### Position Type

#### creates position with line and character

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pos = Position { line: 10, character: 5 }
expect pos.line == 10
expect pos.character == 5
```

</details>

#### handles zero-based positions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val origin = Position { line: 0, character: 0 }
expect origin.line == 0
expect origin.character == 0
```

</details>

#### handles large line numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val large_pos = Position { line: 10000, character: 100 }
expect large_pos.line == 10000
expect large_pos.character == 100
```

</details>

#### compares positions

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val start = Position { line: 0, character: 0 }
val end = Position { line: 0, character: 10 }
val range = Range { start: start, end: end }

expect range.start.line == 0
expect range.end.character == 10
```

</details>

#### handles single-line ranges

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val start = Position { line: 5, character: 0 }
val end = Position { line: 5, character: 20 }
val range = Range { start: start, end: end }

expect range.start.line == range.end.line
```

</details>

#### handles multi-line ranges

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val start = Position { line: 5, character: 0 }
val end = Position { line: 10, character: 20 }
val range = Range { start: start, end: end }

expect range.start.line < range.end.line
```

</details>

#### calculates range length for single line

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val start = Position { line: 0, character: 5 }
val end = Position { line: 0, character: 15 }
val range = Range { start: start, end: end }

val length = end.character - start.character
expect length == 10
```

</details>

### DiagnosticSeverity Enum

#### has Error severity

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val severity = DiagnosticSeverity.Error
match severity:
    case DiagnosticSeverity.Error:
        expect true
    _ =>
        fail "Should be Error"
```

</details>

#### has Warning severity

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val severity = DiagnosticSeverity.Warning
match severity:
    case DiagnosticSeverity.Warning:
        expect true
    _ =>
        fail "Should be Warning"
```

</details>

#### has Information severity

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val severity = DiagnosticSeverity.Information
match severity:
    case DiagnosticSeverity.Information:
        expect true
    _ =>
        fail "Should be Information"
```

</details>

#### has Hint severity

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val severity = DiagnosticSeverity.Hint
match severity:
    case DiagnosticSeverity.Hint:
        expect true
    _ =>
        fail "Should be Hint"
```

</details>

#### distinguishes between severities

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect diag message len
2. expect diag message contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/app/lsp/protocol_types_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
