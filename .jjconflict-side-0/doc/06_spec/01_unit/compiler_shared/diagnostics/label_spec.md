# Label Specification

> <details>

<!-- sdn-diagram:id=label_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=label_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

label_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=label_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Label Specification

## Scenarios

### Label

#### keeps diagnostic label construction and accessors available

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = diagnostics_source("label")

expect(source).to_contain("struct Label")
expect(source).to_contain("span: Span")
expect(source).to_contain("message: text")
expect(source).to_contain("static fn new(span: Span, message: text) -> Label")
expect(source).to_contain("static fn at(line: i64, column: i64, message: text) -> Label")
```

</details>

#### keeps diagnostic label formatting available

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = diagnostics_source("label")

expect(source).to_contain("fn to_string() -> text")
expect(source).to_contain("self.span.to_string()")
expect(source).to_contain("self.message")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/compiler_shared/diagnostics/label_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Label

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
