# Tmp Head Specification

> <details>

<!-- sdn-diagram:id=tmp_head_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tmp_head_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tmp_head_spec -> std
tmp_head_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tmp_head_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tmp Head Specification

## Scenarios

### head

#### 02 len

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val boxes = html_compat_fixture_simple_boxes("02_block_boxes", 320, 240)
expect(boxes.len()).to_equal(6)
expect(boxes[5].y).to_equal(68)
```

</details>

#### missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(html_compat_fixture_simple_boxes("99_missing", 320, 240).len()).to_equal(0)
```

</details>

#### compare

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val simple_boxes = html_compat_fixture_simple_boxes("02_block_boxes", 320, 240)
val report = compare_electron_geometry_json(
    "electron_geometry", "simple_renderer_geometry",
    320, 240,
    "{\"items\":[{\"label\":\"outer\",\"x\":8,\"y\":8,\"width\":304,\"height\":80,\"text\":\"\"},{\"label\":\"header\",\"x\":8,\"y\":8,\"width\":120,\"height\":20,\"text\":\"\"},{\"label\":\"middle\",\"x\":8,\"y\":28,\"width\":304,\"height\":40,\"text\":\"\"},{\"label\":\"left\",\"x\":8,\"y\":28,\"width\":80,\"height\":20,\"text\":\"\"},{\"label\":\"right\",\"x\":8,\"y\":48,\"width\":80,\"height\":20,\"text\":\"\"},{\"label\":\"footer\",\"x\":8,\"y\":68,\"width\":120,\"height\":20,\"text\":\"\"}]}",
    simple_boxes,
    "simple_renderer:02_block_boxes",
    "build/test/electron_geometry.json"
)
expect(report.status).to_equal("layout_match")
expect(report.mismatch_count).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `tmp_head_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- head

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
