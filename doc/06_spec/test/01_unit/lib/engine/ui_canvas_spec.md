# Ui Canvas Specification

> <details>

<!-- sdn-diagram:id=ui_canvas_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ui_canvas_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ui_canvas_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ui_canvas_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ui Canvas Specification

## Scenarios

### Anchor

#### creates top_left anchor

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Anchor.top_left()
expect(a.min_x).to_equal(0.0)
expect(a.min_y).to_equal(0.0)
expect(a.max_x).to_equal(0.0)
expect(a.max_y).to_equal(0.0)
```

</details>

#### creates center anchor

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Anchor.center()
expect(a.min_x).to_equal(0.5)
expect(a.min_y).to_equal(0.5)
```

</details>

#### creates stretch anchor

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Anchor.stretch()
expect(a.min_x).to_equal(0.0)
expect(a.max_x).to_equal(1.0)
expect(a.max_y).to_equal(1.0)
```

</details>

#### creates top_right anchor

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Anchor.top_right()
expect(a.min_x).to_equal(1.0)
expect(a.min_y).to_equal(0.0)
```

</details>

### UIRect

#### detects point inside rect

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = UIRect(x: 10.0, y: 20.0, width: 100.0, height: 50.0)
expect(r.contains_point(50.0, 40.0)).to_equal(true)
```

</details>

#### detects point outside rect

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = UIRect(x: 10.0, y: 20.0, width: 100.0, height: 50.0)
expect(r.contains_point(5.0, 40.0)).to_equal(false)
expect(r.contains_point(50.0, 80.0)).to_equal(false)
```

</details>

#### computes center

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = UIRect(x: 10.0, y: 20.0, width: 100.0, height: 50.0)
expect(r.center_x()).to_equal(60.0)
expect(r.center_y()).to_equal(45.0)
```

</details>

### UIElement

#### creates element with defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val elem = UIElement.new("title", "label", 200.0, 40.0)
expect(elem.name).to_equal("title")
expect(elem.element_type).to_equal("label")
expect(elem.width).to_equal(200.0)
expect(elem.height).to_equal(40.0)
expect(elem.visible).to_equal(true)
expect(elem.parent_index).to_equal(-1)
```

</details>

### UICanvas

#### creates canvas with dimensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val canvas = UICanvas.new(1920.0, 1080.0, "screen")
expect(canvas.element_count()).to_equal(0)
```

</details>

#### adds elements and returns index

1. var canvas = UICanvas new
   - Expected: idx0 equals `0`
   - Expected: idx1 equals `1`
   - Expected: canvas.element_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var canvas = UICanvas.new(800.0, 600.0, "screen")
val idx0 = canvas.add_element(UIElement.new("a", "label", 100.0, 30.0))
val idx1 = canvas.add_element(UIElement.new("b", "button", 120.0, 40.0))
expect(idx0).to_equal(0)
expect(idx1).to_equal(1)
expect(canvas.element_count()).to_equal(2)
```

</details>

#### finds element by name

1. var canvas = UICanvas new
2. canvas add element
3. canvas add element
   - Expected: canvas.find_by_name("footer") equals `1`
   - Expected: canvas.find_by_name("missing") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var canvas = UICanvas.new(800.0, 600.0, "screen")
canvas.add_element(UIElement.new("header", "label", 100.0, 30.0))
canvas.add_element(UIElement.new("footer", "label", 100.0, 30.0))
expect(canvas.find_by_name("footer")).to_equal(1)
expect(canvas.find_by_name("missing")).to_equal(-1)
```

</details>

#### sets parent-child relationship

1. var canvas = UICanvas new
2. canvas add element
3. canvas add element
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var canvas = UICanvas.new(800.0, 600.0, "screen")
canvas.add_element(UIElement.new("parent", "panel", 400.0, 300.0))
canvas.add_element(UIElement.new("child", "label", 100.0, 30.0))
val ok = canvas.set_parent(1, 0)
expect(ok).to_equal(true)
```

</details>

#### rejects invalid parent index

1. var canvas = UICanvas new
2. canvas add element
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var canvas = UICanvas.new(800.0, 600.0, "screen")
canvas.add_element(UIElement.new("only", "label", 100.0, 30.0))
val ok = canvas.set_parent(0, 5)
expect(ok).to_equal(false)
```

</details>

#### toggles visibility

1. var canvas = UICanvas new
2. canvas add element
3. canvas add element
4. canvas set visible
   - Expected: visible.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var canvas = UICanvas.new(800.0, 600.0, "screen")
canvas.add_element(UIElement.new("a", "label", 100.0, 30.0))
canvas.add_element(UIElement.new("b", "label", 100.0, 30.0))
canvas.set_visible(1, false)
val visible = canvas.get_visible_elements()
expect(visible.len()).to_equal(1)
```

</details>

#### sets content

1. var canvas = UICanvas new
2. canvas add element
3. canvas set content
   - Expected: elem.content equals `Score: 42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var canvas = UICanvas.new(800.0, 600.0, "screen")
canvas.add_element(UIElement.new("score", "label", 100.0, 30.0))
canvas.set_content(0, "Score: 42")
if val Some(elem) = canvas.get_element(0):
    expect(elem.content).to_equal("Score: 42")
```

</details>

#### computes rect with top_left anchor

1. var canvas = UICanvas new
2. var elem = UIElement new
3. canvas add element
   - Expected: rect.x equals `50.0`
   - Expected: rect.y equals `30.0`
   - Expected: rect.width equals `200.0`
   - Expected: rect.height equals `100.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var canvas = UICanvas.new(800.0, 600.0, "screen")
var elem = UIElement.new("box", "panel", 200.0, 100.0)
elem.offset_x = 50.0
elem.offset_y = 30.0
canvas.add_element(elem)
val rect = canvas.compute_rect(0)
expect(rect.x).to_equal(50.0)
expect(rect.y).to_equal(30.0)
expect(rect.width).to_equal(200.0)
expect(rect.height).to_equal(100.0)
```

</details>

#### computes rect with center anchor

1. var canvas = UICanvas new
2. var elem = UIElement new
3. elem anchor = Anchor center
4. canvas add element
   - Expected: rect.x equals `400.0`
   - Expected: rect.y equals `300.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var canvas = UICanvas.new(800.0, 600.0, "screen")
var elem = UIElement.new("centered", "panel", 100.0, 50.0)
elem.anchor = Anchor.center()
canvas.add_element(elem)
val rect = canvas.compute_rect(0)
expect(rect.x).to_equal(400.0)
expect(rect.y).to_equal(300.0)
```

</details>

#### clears all elements

1. var canvas = UICanvas new
2. canvas add element
3. canvas add element
   - Expected: canvas.element_count() equals `2`
4. canvas clear
   - Expected: canvas.element_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var canvas = UICanvas.new(800.0, 600.0, "screen")
canvas.add_element(UIElement.new("a", "label", 100.0, 30.0))
canvas.add_element(UIElement.new("b", "button", 120.0, 40.0))
expect(canvas.element_count()).to_equal(2)
canvas.clear()
expect(canvas.element_count()).to_equal(0)
```

</details>

### Widgets

#### creates label with content

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val label = create_label("title", "Hello", 10.0, 20.0, 200.0, 30.0)
expect(label.name).to_equal("title")
expect(label.element_type).to_equal("label")
expect(label.content).to_equal("Hello")
expect(label.offset_x).to_equal(10.0)
expect(label.offset_y).to_equal(20.0)
```

</details>

#### creates button

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val btn = create_button("ok", "OK", 5.0, 10.0, 100.0, 40.0)
expect(btn.element_type).to_equal("button")
expect(btn.content).to_equal("OK")
```

</details>

#### creates panel

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val panel = create_panel("bg", 0.0, 0.0, 800.0, 600.0)
expect(panel.element_type).to_equal("panel")
```

</details>

#### creates progress bar

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = create_progress_bar("hp", 10.0, 10.0, 200.0, 20.0)
expect(bar.element_type).to_equal("progress_bar")
expect(bar.content).to_equal("0")
```

</details>

#### creates image

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val img = create_image("logo", "logo.png", 0.0, 0.0, 64.0, 64.0)
expect(img.element_type).to_equal("image")
expect(img.content).to_equal("logo.png")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/ui_canvas_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Anchor
- UIRect
- UIElement
- UICanvas
- Widgets

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
