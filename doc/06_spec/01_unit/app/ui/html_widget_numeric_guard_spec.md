# Html Widget Numeric Guard Specification

> <details>

<!-- sdn-diagram:id=html_widget_numeric_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=html_widget_numeric_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

html_widget_numeric_guard_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=html_widget_numeric_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Html Widget Numeric Guard Specification

## Scenarios

### html widget numeric guards

#### guards widget property integer parsing

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/ui.render/html_widgets.spl") ?? ""

expect(source).to_contain("fn html_int_or(value: text, default_value: i64) -> i64")
expect(source).to_contain("html_int_or(sel_str, -1)")
expect(source).to_contain("html_int_or(active_idx_str, 0)")
expect(source).to_contain("html_int_or(active_str, 0)")
expect(source).to_contain("html_int_or(active_idx_str, -1)")
expect(source).to_contain("trimmed.to_int() ?? default_value")
expect(source.contains("sel_str.to_int()")).to_equal(false)
expect(source.contains("active_idx_str.to_int()")).to_equal(false)
expect(source.contains("active_str.to_int()")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/html_widget_numeric_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- html widget numeric guards

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
