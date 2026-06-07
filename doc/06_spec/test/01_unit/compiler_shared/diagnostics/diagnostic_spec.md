# Diagnostic Specification

> <details>

<!-- sdn-diagram:id=diagnostic_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=diagnostic_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

diagnostic_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=diagnostic_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Diagnostic Specification

## Scenarios

### Diagnostic

#### keeps diagnostic fields and factory constructors available

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = diagnostics_source("diagnostic")

expect(source).to_contain("struct Diagnostic")
expect(source).to_contain("severity: Severity")
expect(source).to_contain("code: text?")
expect(source).to_contain("static fn new(severity: Severity, message: text) -> Diagnostic")
expect(source).to_contain("static fn error(message: text) -> Diagnostic")
expect(source).to_contain("static fn warning(message: text) -> Diagnostic")
```

</details>

#### keeps diagnostic builder and display helpers available

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = diagnostics_source("diagnostic")

expect(source).to_contain("fn with_code(code: text) -> Diagnostic")
expect(source).to_contain("fn with_span(span: Span) -> Diagnostic")
expect(source).to_contain("fn with_label(span: Span, message: text) -> Diagnostic")
expect(source).to_contain("fn to_string_with_span() -> text")
expect(source).to_contain("fn item_count() -> i64")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/compiler_shared/diagnostics/diagnostic_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Diagnostic

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
