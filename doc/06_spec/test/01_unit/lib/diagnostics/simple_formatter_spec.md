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
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Formatter Specification

## Scenarios

### Simple Formatter

#### keeps minimal compiler diagnostic creation available

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = diagnostic_source("diagnostic.spl")

expect(source).to_contain("struct Diagnostic:")
expect(source).to_contain("static fn new(severity: Severity, message: text) -> Diagnostic")
expect(source).to_contain("static fn error(message: text) -> Diagnostic")
expect(source).to_contain("static fn warning(message: text) -> Diagnostic")
expect(source).to_contain("static fn note(message: text) -> Diagnostic")
expect(source).to_contain("static fn help_msg(message: text) -> Diagnostic")
```

</details>

#### keeps simple diagnostic display helpers available

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = diagnostic_source("diagnostic.spl")

expect(source).to_contain("fn to_string() -> text")
expect(source).to_contain("fn to_string_with_span() -> text")
expect(source).to_contain("fn item_count() -> i64")
expect(source).to_contain("fn with_code(code: text) -> Diagnostic")
expect(source).to_contain("fn with_label(span: Span, message: text) -> Diagnostic")
expect(source).to_contain("fn with_help(help: text) -> Diagnostic")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/diagnostics/simple_formatter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Simple Formatter

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
