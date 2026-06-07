# Simple Formatter Specification

> <details>

<!-- sdn-diagram:id=simple_formatter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_formatter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_formatter_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_formatter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Formatter Specification

## Scenarios

### Simple Formatter

#### should define the canonical diagnostic structure

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/00.common/diagnostics/diagnostic.spl")
expect(src.contains("struct Diagnostic")).to_equal(true)
expect(src.contains("severity: Severity")).to_equal(true)
expect(src.contains("code: text?")).to_equal(true)
expect(src.contains("message: text")).to_equal(true)
expect(src.contains("labels: [Label]")).to_equal(true)
expect(src.contains("notes: [text]")).to_equal(true)
```

</details>

#### should expose diagnostic constructors for display severities

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/00.common/diagnostics/diagnostic.spl")
expect(src.contains("static fn error(message: text) -> Diagnostic")).to_equal(true)
expect(src.contains("static fn warning(message: text) -> Diagnostic")).to_equal(true)
expect(src.contains("static fn note(message: text) -> Diagnostic")).to_equal(true)
expect(src.contains("static fn help_msg(message: text) -> Diagnostic")).to_equal(true)
expect(src.contains("static fn info(message: text) -> Diagnostic")).to_equal(true)
```

</details>

#### should support builder methods for code span labels notes and help

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/00.common/diagnostics/diagnostic.spl")
expect(src.contains("fn with_code(code: text) -> Diagnostic")).to_equal(true)
expect(src.contains("fn with_span(span: Span) -> Diagnostic")).to_equal(true)
expect(src.contains("fn with_label(span: Span, message: text) -> Diagnostic")).to_equal(true)
expect(src.contains("fn with_note(note: text) -> Diagnostic")).to_equal(true)
expect(src.contains("fn with_help(help: text) -> Diagnostic")).to_equal(true)
```

</details>

#### should format simple diagnostics with optional code and span

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/00.common/diagnostics/diagnostic.spl")
expect(src.contains("fn to_string() -> text")).to_equal(true)
expect(src.contains("self.code.unwrap()")).to_equal(true)
expect(src.contains("self.message")).to_equal(true)
expect(src.contains("fn to_string_with_span() -> text")).to_equal(true)
expect(src.contains("span.to_string()")).to_equal(true)
expect(src.contains("self.to_string()")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/diagnostics/simple_formatter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Simple Formatter

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
