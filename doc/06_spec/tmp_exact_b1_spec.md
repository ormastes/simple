# Tmp Exact B1 Specification

> <details>

<!-- sdn-diagram:id=tmp_exact_b1_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tmp_exact_b1_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tmp_exact_b1_spec -> std
tmp_exact_b1_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tmp_exact_b1_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tmp Exact B1 Specification

## Scenarios

### b1

#### 07

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val simple_boxes = html_compat_fixture_simple_boxes("07_scrollable_list", 320, 240)
expect(simple_boxes.len()).to_equal(5)
expect(simple_boxes[0].label).to_equal("scroll_shell")
expect(simple_boxes[0].x).to_equal(12)
expect(simple_boxes[0].width).to_equal(68)
expect(simple_boxes[0].height).to_equal(38)
expect(simple_boxes[1].label).to_equal("scroll_list")
expect(simple_boxes[1].width).to_equal(45)
expect(simple_boxes[2].label).to_equal("scroll_item_0")
expect(simple_boxes[2].width).to_equal(42)
expect(simple_boxes[4].label).to_equal("scroll_item_2")
expect(simple_boxes[4].y).to_equal(32)
```

</details>

#### 13

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val simple_boxes = html_compat_fixture_simple_boxes("13_margin", 320, 240)
expect(simple_boxes.len()).to_equal(6)
expect(simple_boxes[0].label).to_equal("outer")
expect(simple_boxes[0].x).to_equal(4)
expect(simple_boxes[0].width).to_equal(312)
expect(simple_boxes[0].height).to_equal(150)
expect(simple_boxes[2].label).to_equal("middle")
expect(simple_boxes[2].y).to_equal(44)
expect(simple_boxes[2].height).to_equal(74)
expect(simple_boxes[5].label).to_equal("footer")
expect(simple_boxes[5].y).to_equal(120)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `tmp_exact_b1_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- b1

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
