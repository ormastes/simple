# Entity Span Specification

> <details>

<!-- sdn-diagram:id=entity_span_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=entity_span_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

entity_span_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=entity_span_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Entity Span Specification

## Scenarios

### Entity Span

#### keeps canonical span fields and constructors available

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = span_source()

expect(source).to_contain("# This is the CANONICAL Span definition for the entire compiler.")
expect(source).to_contain("struct Span:")
expect(source).to_contain("start: i64")
expect(source).to_contain("end: i64")
expect(source).to_contain("line: i64")
expect(source).to_contain("col: i64")
expect(source).to_contain("static fn new(start: i64, end: i64, line: i64, col: i64) -> Span")
expect(source).to_contain("static fn empty() -> Span")
```

</details>

#### keeps span merge and formatting helpers available

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = span_source()

expect(source).to_contain("fn to(other: Span) -> Span")
expect(source).to_contain("fn merge(other: Span) -> Span")
expect(source).to_contain("fn len() -> i64")
expect(source).to_contain("fn is_empty() -> bool")
expect(source).to_contain("fn to_string() -> text")
expect(source).to_contain("fn to_range_string() -> text")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/entity/entity_span_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Entity Span

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
