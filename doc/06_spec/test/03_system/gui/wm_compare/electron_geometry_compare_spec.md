# Electron Geometry Compare Specification

> <details>

<!-- sdn-diagram:id=electron_geometry_compare_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=electron_geometry_compare_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

electron_geometry_compare_spec -> std
electron_geometry_compare_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=electron_geometry_compare_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Electron Geometry Compare Specification

## Scenarios

### wm_compare electron geometry compare

#### converts Electron geometry JSON into structural layout boxes

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val geometry_json = "{\"producer\":\"electron-chromium-geometry\",\"viewport\":{\"width\":320,\"height\":240},\"items\":[{\"label\":\"header\",\"tag\":\"div\",\"x\":8,\"y\":8,\"width\":120,\"height\":20,\"text\":\"\"},{\"label\":\"footer\",\"tag\":\"div\",\"x\":8,\"y\":68,\"width\":120,\"height\":20,\"text\":\"\"}]}"
val boxes = electron_geometry_json_to_boxes(geometry_json)
expect(boxes.len()).to_equal(2)
expect(boxes[0].label).to_equal("header")
expect(boxes[0].x).to_equal(8)
expect(boxes[0].width).to_equal(120)
expect(boxes[1].label).to_equal("footer")
expect(boxes[1].y).to_equal(68)
```

</details>

#### compares Electron geometry JSON against Simple-side boxes

- structural layout box
- structural layout box
   - Expected: report.status equals `layout_mismatch`
   - Expected: report.mismatch_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val geometry_json = "{\"producer\":\"electron-chromium-geometry\",\"viewport\":{\"width\":320,\"height\":240},\"items\":[{\"label\":\"header\",\"tag\":\"div\",\"x\":8,\"y\":8,\"width\":120,\"height\":20,\"text\":\"\"},{\"label\":\"footer\",\"tag\":\"div\",\"x\":8,\"y\":68,\"width\":120,\"height\":20,\"text\":\"\"}]}"
val simple_boxes = [
    structural_layout_box("header", 8, 8, 120, 20, ""),
    structural_layout_box("footer", 8, 72, 120, 20, "")
]
val report = compare_electron_geometry_json(
    "electron_geometry", "simple_layout",
    320, 240,
    geometry_json, simple_boxes,
    "runtime_evidence selected=electron_geometry;status=Initialized",
    "test/09_baselines/html_compat/02_block_boxes/report.sdn"
)
expect(report.status).to_equal("layout_mismatch")
expect(report.mismatch_count).to_equal(1)
val sdn = structural_box_layout_report_sdn(report, electron_geometry_json_to_boxes(geometry_json), simple_boxes)
expect(sdn).to_contain("label: \"header\"")
expect(sdn).to_contain("label: \"footer\"")
expect(sdn).to_contain("y: 72")
```

</details>

#### fails closed for malformed geometry JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val boxes = electron_geometry_json_to_boxes("{\"items\": [}")
expect(boxes.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/wm_compare/electron_geometry_compare_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- wm_compare electron geometry compare

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
