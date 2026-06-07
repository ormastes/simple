# I18n Context Specification

> <details>

<!-- sdn-diagram:id=i18n_context_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=i18n_context_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

i18n_context_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=i18n_context_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# I18n Context Specification

## Scenarios

### I18N Context

#### should define severity names colors and priorities

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/00.common/diagnostics/severity.spl")
expect(src.contains("enum Severity")).to_equal(true)
expect(src.contains("Severity.Error: \"error\"")).to_equal(true)
expect(src.contains("Severity.Warning: \"warning\"")).to_equal(true)
expect(src.contains("fn color() -> text")).to_equal(true)
expect(src.contains("fn priority() -> i32")).to_equal(true)
```

</details>

#### should expose severity predicates used by diagnostics

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/00.common/diagnostics/severity.spl")
expect(src.contains("fn is_error() -> bool")).to_equal(true)
expect(src.contains("Severity.Error: true")).to_equal(true)
expect(src.contains("fn is_warning() -> bool")).to_equal(true)
expect(src.contains("Severity.Warning: true")).to_equal(true)
```

</details>

#### should define source spans with constructors and range formatting

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/00.common/diagnostics/span.spl")
expect(src.contains("struct Span")).to_equal(true)
expect(src.contains("static fn new(start: i64, end: i64, line: i64, col: i64) -> Span")).to_equal(true)
expect(src.contains("static fn default() -> Span")).to_equal(true)
expect(src.contains("fn to_range_string() -> text")).to_equal(true)
expect(src.contains("val end_col = self.col + (self.end - self.start)")).to_equal(true)
```

</details>

#### should define labels that bind messages to spans

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/00.common/diagnostics/label.spl")
expect(src.contains("struct Label")).to_equal(true)
expect(src.contains("static fn new(span: Span, message: text) -> Label")).to_equal(true)
expect(src.contains("static fn at(line: i64, column: i64, message: text) -> Label")).to_equal(true)
expect(src.contains("fn to_string() -> text")).to_equal(true)
expect(src.contains("self.span.to_string()")).to_equal(true)
expect(src.contains("self.message")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/diagnostics/i18n_context_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- I18N Context

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
