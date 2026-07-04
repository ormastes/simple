# Tmp Shrink Specification

> <details>

<!-- sdn-diagram:id=tmp_shrink_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tmp_shrink_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tmp_shrink_spec -> std
tmp_shrink_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tmp_shrink_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tmp Shrink Specification

## Scenarios

### tmp shrink

#### prints shrink fixture

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val simple_boxes = html_compat_fixture_simple_boxes("19_flex_shrink_weights", 320, 240)
expect(simple_boxes.len()).to_equal(4)
print "0:{simple_boxes[0].width}"
print "1:{simple_boxes[1].width}"
print "2:{simple_boxes[2].x}:{simple_boxes[2].width}"
print "3:{simple_boxes[3].x}:{simple_boxes[3].width}"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `tmp_shrink_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- tmp shrink

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
