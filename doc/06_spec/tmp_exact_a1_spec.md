# Tmp Exact A1 Specification

> <details>

<!-- sdn-diagram:id=tmp_exact_a1_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tmp_exact_a1_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tmp_exact_a1_spec -> std
tmp_exact_a1_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tmp_exact_a1_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tmp Exact A1 Specification

## Scenarios

### a1

#### 03

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val simple_boxes = html_compat_fixture_simple_boxes("03_list", 320, 240)
expect(simple_boxes.len()).to_equal(4)
expect(simple_boxes[0].label).to_equal("list_root")
expect(simple_boxes[0].x).to_equal(8)
expect(simple_boxes[0].width).to_equal(304)
expect(simple_boxes[1].label).to_equal("list_item_0")
expect(simple_boxes[1].width).to_equal(80)
expect(simple_boxes[1].height).to_equal(12)
expect(simple_boxes[3].label).to_equal("list_item_2")
expect(simple_boxes[3].y).to_equal(32)
```

</details>

#### 04

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val simple_boxes = html_compat_fixture_simple_boxes("04_button", 320, 240)
expect(simple_boxes.len()).to_equal(2)
expect(simple_boxes[0].label).to_equal("button_panel")
expect(simple_boxes[0].x).to_equal(18)
expect(simple_boxes[0].width).to_equal(204)
expect(simple_boxes[0].height).to_equal(63)
expect(simple_boxes[1].label).to_equal("primary_button")
expect(simple_boxes[1].x).to_equal(30)
expect(simple_boxes[1].width).to_equal(120)
expect(simple_boxes[1].height).to_equal(36)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `tmp_exact_a1_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- a1

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
