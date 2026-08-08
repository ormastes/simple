# Layout Numeric Guard Specification

> <details>

<!-- sdn-diagram:id=layout_numeric_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=layout_numeric_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

layout_numeric_guard_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=layout_numeric_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Layout Numeric Guard Specification

## Scenarios

### ui layout numeric guard

#### defaults malformed layout numeric properties

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/lib/common/ui/layout.spl") ?? ""

expect(source).to_contain("val max_h = max_h_str.to_int() ?? 0")
expect(source).to_contain("return w.to_int() ?? 0")
expect(source).to_contain("return h.to_int() ?? 0")
expect(source).to_contain("return rows.to_int() ?? 0")
expect(source).to_contain("return f.to_int() ?? 1")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/ui/layout_numeric_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ui layout numeric guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
