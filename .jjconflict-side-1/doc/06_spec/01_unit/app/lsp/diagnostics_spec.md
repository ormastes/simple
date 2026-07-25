# Diagnostics Specification

> <details>

<!-- sdn-diagram:id=diagnostics_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=diagnostics_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

diagnostics_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=diagnostics_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Diagnostics Specification

## Scenarios

### Position

#### creates position with line and character

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pos = Position.new(10, 5)
expect pos.line == 10
expect pos.character == 5
```

</details>

#### starts at zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pos = Position.new(0, 0)
expect pos.line == 0
expect pos.character == 0
```

</details>

### Range

#### creates range from positions

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val start = Position.new(0, 0)
val end = Position.new(0, 10)
val range = Range.new(start, end)
expect range.start.line == 0
expect range.end.character == 10
```

</details>

#### supports multi-line ranges

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val start = Position.new(5, 0)
val end = Position.new(10, 20)
val range = Range.new(start, end)
expect range.start.line == 5
expect range.end.line == 10
```

</details>

### DiagnosticSeverity

#### has Error severity

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect DiagnosticSeverity.Error == DiagnosticSeverity.Error
```

</details>

#### has Warning severity

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect DiagnosticSeverity.Warning == DiagnosticSeverity.Warning
```

</details>

#### has Information severity

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect DiagnosticSeverity.Information == DiagnosticSeverity.Information
```

</details>

#### has Hint severity

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect DiagnosticSeverity.Hint == DiagnosticSeverity.Hint
```

</details>

### Diagnostic

#### creates diagnostic with range and message

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val range = Range.new(Position.new(0, 0), Position.new(0, 5))
val diag = Diagnostic.new(range, DiagnosticSeverity.Error, "Syntax error")
expect diag.message == "Syntax error"
expect diag.severity == DiagnosticSeverity.Error
```

</details>

#### adds source

1.  with source


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val range = Range.new(Position.new(0, 0), Position.new(0, 5))
val diag = Diagnostic.new(range, DiagnosticSeverity.Warning, "Unused variable")
    .with_source("simple-lint")
expect diag.source != nil
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/lsp/diagnostics_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Position
- Range
- DiagnosticSeverity
- Diagnostic

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
