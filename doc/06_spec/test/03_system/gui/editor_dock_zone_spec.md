# Editor Dock Zone Specification

> <details>

<!-- sdn-diagram:id=editor_dock_zone_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=editor_dock_zone_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

editor_dock_zone_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=editor_dock_zone_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Dock Zone Specification

## Scenarios

### dock zone — constants and structs

#### defines dock positions

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/dock_zone.spl")
expect(src.contains("enum DockPosition:")).to_equal(true)
expect(src.contains("Left")).to_equal(true)
expect(src.contains("Right")).to_equal(true)
expect(src.contains("Bottom")).to_equal(true)
```

</details>

#### defines DockZone struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/dock_zone.spl")
expect(src.contains("struct DockZone:")).to_equal(true)
expect(src.contains("id: i64")).to_equal(true)
expect(src.contains("position: DockPosition")).to_equal(true)
expect(src.contains("size: i64")).to_equal(true)
expect(src.contains("visible: bool")).to_equal(true)
```

</details>

#### defines DockLayout class

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/dock_zone.spl")
expect(src.contains("class DockLayout:")).to_equal(true)
expect(src.contains("left: DockZone")).to_equal(true)
expect(src.contains("right: DockZone")).to_equal(true)
expect(src.contains("bottom: DockZone")).to_equal(true)
expect(src.contains("active_right: text")).to_equal(true)
expect(src.contains("right_visible: bool")).to_equal(true)
```

</details>

### dock zone — mutations

#### has toggle helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/dock_zone.spl")
expect(src.contains("fn dock_zone_toggle(zone: DockZone) -> DockZone")).to_equal(true)
expect(src.contains("me toggle_left() -> DockLayout")).to_equal(true)
expect(src.contains("me toggle_right() -> DockLayout")).to_equal(true)
expect(src.contains("me toggle_bottom() -> DockLayout")).to_equal(true)
```

</details>

#### has right panel visibility methods

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/dock_zone.spl")
expect(src.contains("me show_right(panel: text)")).to_equal(true)
expect(src.contains("me hide_right()")).to_equal(true)
expect(src.contains("fn active_right_panel() -> text")).to_equal(true)
```

</details>

#### has width and visibility queries

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/dock_zone.spl")
expect(src.contains("me left_width_value() -> i64")).to_equal(true)
expect(src.contains("me right_width_value() -> i64")).to_equal(true)
expect(src.contains("me is_right_visible() -> bool")).to_equal(true)
```

</details>

### dock zone — queries

#### has factory functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/dock_zone.spl")
expect(src.contains("fn dock_zone_new(id: i64, position: DockPosition) -> DockZone")).to_equal(true)
expect(src.contains("static fn new() -> DockLayout")).to_equal(true)
```

</details>

#### creates and toggles zones

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val zone = dock_zone_new(7, DockPosition.Right)
expect(zone.id).to_equal(7)
expect(zone.size).to_equal(250)
expect(zone.visible).to_equal(true)
val toggled = dock_zone_toggle(zone)
expect(toggled.id).to_equal(7)
expect(toggled.visible).to_equal(false)
```

</details>

#### tracks right panel visibility

1. layout show right
   - Expected: layout.right_visible is true
   - Expected: layout.active_right_panel() equals `outline`
2. layout hide right
   - Expected: layout.right_visible is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layout = DockLayout.new()
expect(layout.right_visible).to_equal(false)
layout.show_right("outline")
expect(layout.right_visible).to_equal(true)
expect(layout.active_right_panel()).to_equal("outline")
layout.hide_right()
expect(layout.right_visible).to_equal(false)
```

</details>

### status bar — struct and functions

#### defines StatusBarIndicators struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/status_bar_indicators.spl")
expect(src.contains("struct StatusBarIndicators:")).to_equal(true)
expect(src.contains("mode: text")).to_equal(true)
expect(src.contains("language_id: text")).to_equal(true)
expect(src.contains("encoding: text")).to_equal(true)
expect(src.contains("error_count: i64")).to_equal(true)
expect(src.contains("warning_count: i64")).to_equal(true)
expect(src.contains("git_branch: text")).to_equal(true)
```

</details>

#### has status_bar_indicators_new

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/status_bar_indicators.spl")
expect(src.contains("fn status_bar_indicators_new() -> StatusBarIndicators")).to_equal(true)
```

</details>

#### has status_bar_indicators_render_left

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/status_bar_indicators.spl")
expect(src.contains("fn status_bar_indicators_render_left(bar: StatusBarIndicators) -> text")).to_equal(true)
```

</details>

#### has status_bar_indicators_render_right

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/status_bar_indicators.spl")
expect(src.contains("fn status_bar_indicators_render_right(bar: StatusBarIndicators) -> text")).to_equal(true)
```

</details>

#### renders diagnostic and cursor indicators

1. var bar = status bar indicators new
   - Expected: status_bar_indicators_render_left(bar) equals ` NORMAL `
   - Expected: right contains `E:1`
   - Expected: right contains `W:3`
   - Expected: right contains `spl`
   - Expected: right contains `3:5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bar = status_bar_indicators_new()
bar.language_id = "spl"
bar.line = 2
bar.col = 4
bar.error_count = 1
bar.warning_count = 3
val right = status_bar_indicators_render_right(bar)
expect(status_bar_indicators_render_left(bar)).to_equal(" NORMAL ")
expect(right.contains("E:1")).to_equal(true)
expect(right.contains("W:3")).to_equal(true)
expect(right.contains("spl")).to_equal(true)
expect(right.contains("3:5")).to_equal(true)
```

</details>

### session — dock layout integration

#### has dock_layout field on EditSession

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/session.spl")
expect(src.contains("dock_layout: DockLayout")).to_equal(true)
```

</details>

#### initializes dock_layout with default in constructor

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/session.spl")
expect(src.contains("dock_layout: DockLayout.new()")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/editor_dock_zone_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- dock zone — constants and structs
- dock zone — mutations
- dock zone — queries
- status bar — struct and functions
- session — dock layout integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
