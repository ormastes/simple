# Engine Ui Facade Specification

> 1. var canvas = UICanvas new

<!-- sdn-diagram:id=engine_ui_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=engine_ui_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

engine_ui_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=engine_ui_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine Ui Facade Specification

## Scenarios

### gc_async_mut engine ui facade

#### re-exports canvas layout and element mutation helpers

1. var canvas = UICanvas new
   - Expected: canvas.element_count() equals `2`
   - Expected: canvas.find_by_name("title") equals `label_idx`
   - Expected: canvas.set_parent(label_idx, panel_idx) is true
   - Expected: canvas.set_content(label_idx, "World") is true
   - Expected: canvas.set_visible(panel_idx, false) is true
   - Expected: canvas.get_visible_elements().length() equals `1`
   - Expected: rect.x equals `10.0`
   - Expected: rect.y equals `20.0`
   - Expected: rect.contains_point(20.0, 25.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var canvas = UICanvas.new(800.0, 600.0, "screen")
val panel = UIElement.new("panel", "panel", 200.0, 100.0)
val panel_idx = canvas.add_element(panel)
val label_idx = canvas.add_element(create_label("title", "Hello", 10.0, 20.0, 120.0, 30.0))

expect(canvas.element_count()).to_equal(2)
expect(canvas.find_by_name("title")).to_equal(label_idx)
expect(canvas.set_parent(label_idx, panel_idx)).to_equal(true)
expect(canvas.set_content(label_idx, "World")).to_equal(true)
expect(canvas.set_visible(panel_idx, false)).to_equal(true)
expect(canvas.get_visible_elements().length()).to_equal(1)

val rect = canvas.compute_rect(label_idx)
expect(rect.x).to_equal(10.0)
expect(rect.y).to_equal(20.0)
expect(rect.contains_point(20.0, 25.0)).to_equal(true)
```

</details>

#### re-exports common widget constructors and anchors

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val center = Anchor.center()
expect(center.min_x).to_equal(0.5)
val button = create_button("ok", "OK", 1.0, 2.0, 80.0, 24.0)
expect(button.element_type).to_equal("button")
val progress = create_progress_bar("load", 0.0, 0.0, 100.0, 12.0)
expect(progress.content).to_equal("0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/engine/ui/engine_ui_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut engine ui facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
