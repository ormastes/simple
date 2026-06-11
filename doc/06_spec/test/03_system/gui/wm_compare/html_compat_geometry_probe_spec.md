# Html Compat Geometry Probe Specification

> <details>

<!-- sdn-diagram:id=html_compat_geometry_probe_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=html_compat_geometry_probe_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

html_compat_geometry_probe_spec -> std
html_compat_geometry_probe_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=html_compat_geometry_probe_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Html Compat Geometry Probe Specification

## Scenarios

### wm_compare html_compat geometry probe

#### exports current Simple renderer boxes for 02_block_boxes

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val boxes = html_compat_fixture_simple_boxes("02_block_boxes", 320, 240)
expect(boxes.len()).to_equal(6)
expect(boxes[0].label).to_equal("outer")
expect(boxes[0].x).to_equal(8)
expect(boxes[0].width).to_equal(304)
expect(boxes[0].height).to_equal(80)
expect(boxes[2].label).to_equal("middle")
expect(boxes[2].width).to_equal(304)
expect(boxes[5].label).to_equal("footer")
expect(boxes[5].y).to_equal(68)
```

</details>

#### returns an empty model for unsupported fixtures

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(html_compat_fixture_simple_boxes("99_missing", 320, 240).len()).to_equal(0)
```

</details>

#### matches live-style Electron geometry when it agrees with the real renderer boxes

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

#### matches the focused list fixture geometry

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

#### matches the focused button fixture geometry

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

#### matches the focused text-input fixture geometry

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val simple_boxes = html_compat_fixture_simple_boxes("05_text_input", 320, 240)
expect(simple_boxes.len()).to_equal(2)
expect(simple_boxes[0].label).to_equal("panel")
expect(simple_boxes[0].x).to_equal(18)
expect(simple_boxes[0].width).to_equal(234)
expect(simple_boxes[0].height).to_equal(56)
expect(simple_boxes[1].label).to_equal("search_input")
expect(simple_boxes[1].x).to_equal(30)
expect(simple_boxes[1].width).to_equal(166)
expect(simple_boxes[1].height).to_equal(32)
```

</details>

#### matches the focused card panel fixture geometry

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val simple_boxes = html_compat_fixture_simple_boxes("06_card_panel", 320, 240)
expect(simple_boxes.len()).to_equal(3)
expect(simple_boxes[0].label).to_equal("card_panel")
expect(simple_boxes[0].x).to_equal(16)
expect(simple_boxes[0].width).to_equal(240)
expect(simple_boxes[0].height).to_equal(90)
expect(simple_boxes[0].text).to_equal("Panel Status ready")
expect(simple_boxes[1].label).to_equal("card_title")
expect(simple_boxes[1].text).to_equal("Panel")
expect(simple_boxes[2].label).to_equal("card_body")
expect(simple_boxes[2].text).to_equal("Status ready")
```

</details>

#### matches the focused scrollable list fixture geometry

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

#### matches the focused margin CSS fixture geometry

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

#### matches the focused border CSS fixture geometry

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val simple_boxes = html_compat_fixture_simple_boxes("14_border", 320, 240)
expect(simple_boxes.len()).to_equal(6)
expect(simple_boxes[0].label).to_equal("outer")
expect(simple_boxes[0].x).to_equal(4)
expect(simple_boxes[0].width).to_equal(312)
expect(simple_boxes[0].height).to_equal(162)
expect(simple_boxes[2].label).to_equal("middle")
expect(simple_boxes[2].y).to_equal(47)
expect(simple_boxes[2].height).to_equal(80)
expect(simple_boxes[5].label).to_equal("footer")
expect(simple_boxes[5].y).to_equal(129)
```

</details>

#### matches the focused flex-row CSS fixture geometry

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val simple_boxes = html_compat_fixture_simple_boxes("16_flex_row", 320, 240)
expect(simple_boxes.len()).to_equal(6)
expect(simple_boxes[0].label).to_equal("outer")
expect(simple_boxes[0].x).to_equal(4)
expect(simple_boxes[0].width).to_equal(312)
expect(simple_boxes[0].height).to_equal(134)
expect(simple_boxes[2].label).to_equal("middle")
expect(simple_boxes[2].y).to_equal(49)
expect(simple_boxes[2].height).to_equal(48)
expect(simple_boxes[4].label).to_equal("right")
expect(simple_boxes[4].x).to_equal(118)
expect(simple_boxes[5].label).to_equal("footer")
expect(simple_boxes[5].y).to_equal(101)
```

</details>

#### matches the focused flex-column CSS fixture geometry

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val simple_boxes = html_compat_fixture_simple_boxes("17_flex_col", 320, 240)
expect(simple_boxes.len()).to_equal(6)
expect(simple_boxes[0].label).to_equal("outer")
expect(simple_boxes[0].x).to_equal(4)
expect(simple_boxes[0].width).to_equal(312)
expect(simple_boxes[0].height).to_equal(168)
expect(simple_boxes[2].label).to_equal("middle")
expect(simple_boxes[2].y).to_equal(49)
expect(simple_boxes[2].height).to_equal(82)
expect(simple_boxes[4].label).to_equal("right")
expect(simple_boxes[4].y).to_equal(92)
expect(simple_boxes[5].label).to_equal("footer")
expect(simple_boxes[5].y).to_equal(135)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/wm_compare/html_compat_geometry_probe_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- wm_compare html_compat geometry probe

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
