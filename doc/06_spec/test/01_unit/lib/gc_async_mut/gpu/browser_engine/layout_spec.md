# Layout Specification

> <details>

<!-- sdn-diagram:id=layout_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=layout_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

layout_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=layout_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Layout Specification

## Scenarios

### browser layout

#### lays out stacked child boxes in source order

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val box = layout_tree(_stacked_dom(), 100.0, 80.0)

expect(box.children.len()).to_equal(2)
expect(box.children[0].y).to_equal(2.0)
expect(box.children[1].y).to_equal(12.0)
expect(box.height).to_equal(24.0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/layout_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- browser layout

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
