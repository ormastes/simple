# Math Repr Specification

> <details>

<!-- sdn-diagram:id=math_repr_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=math_repr_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

math_repr_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=math_repr_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Math Repr Specification

## Scenarios

### Math Repr

#### keeps public math rendering entrypoints available

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = math_repr_source()

expect(source).to_contain("fn render_latex_raw(expr: text) -> text")
expect(source).to_contain("fn to_pretty(expr: text) -> text")
expect(source).to_contain("fn to_text(expr: text) -> text")
expect(source).to_contain("fn to_debug(expr: text) -> text")
expect(source).to_contain("fn to_md(expr: text) -> text")
```

</details>

#### keeps latex, pretty, text, and debug parser pipelines available

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = math_repr_source()

expect(source).to_contain("fn _expr_latex(tokens: [text], pos: i64) -> [text]")
expect(source).to_contain("fn _expr_pretty(tokens: [text], pos: i64) -> [text]")
expect(source).to_contain("fn _expr_text(tokens: [text], pos: i64) -> [text]")
expect(source).to_contain("fn _expr_debug(tokens: [text], pos: i64) -> [text]")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/math_repr_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Math Repr

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
