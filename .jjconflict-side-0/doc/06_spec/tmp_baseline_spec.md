# Tmp Baseline Specification

> <details>

<!-- sdn-diagram:id=tmp_baseline_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tmp_baseline_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tmp_baseline_spec -> std
tmp_baseline_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tmp_baseline_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tmp Baseline Specification

## Scenarios

### tmp baseline

#### matches baseline fixture

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val simple_boxes = html_compat_fixture_simple_boxes("22_flex_align_items_baseline", 320, 240)
expect(simple_boxes.len()).to_equal(3)
expect(simple_boxes[0].label).to_equal("baseline_shell")
expect(simple_boxes[0].width).to_equal(220)
expect(simple_boxes[0].height).to_equal(32)
expect(simple_boxes[0].text).to_equal("A B")
expect(simple_boxes[1].label).to_equal("baseline_big")
expect(simple_boxes[1].width).to_equal(23)
expect(simple_boxes[1].text).to_equal("A")
expect(simple_boxes[2].label).to_equal("baseline_small")
expect(simple_boxes[2].x).to_equal(39)
expect(simple_boxes[2].y).to_equal(30)
expect(simple_boxes[2].width).to_equal(11)
expect(simple_boxes[2].text).to_equal("B")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `tmp_baseline_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- tmp baseline

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
