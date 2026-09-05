# Engine Merge Specification

> <details>

<!-- sdn-diagram:id=engine_merge_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=engine_merge_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

engine_merge_spec -> app
engine_merge_spec -> std
engine_merge_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=engine_merge_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine Merge Specification

## Scenarios

### Chromium engine merge — construction

#### constructs a ChromiumEngine with the viewport it was given

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val engine = ChromiumEngine.new(VIEWPORT_W, VIEWPORT_H)
expect(engine.width() == VIEWPORT_W).to_be_true()
expect(engine.height() == VIEWPORT_H).to_be_true()
```

</details>

#### uses the canonical BeDomNode type for the shell root builder

1. var root: BeDomNode = engine merge root


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# If this compiles, the shell's root builder returns the same
# BeDomNode type the canonical layout engine consumes — i.e.
# the two engines have in fact been merged onto one import.
var root: BeDomNode = engine_merge_root("#101010FF")
expect(be_dom_get_children(root).len() == 0).to_be_true()
```

</details>

### Chromium engine merge — layout pass

#### lays out a single-panel DOM to a non-degenerate box

1. var root: BeDomNode = engine merge root
2. be dom add child


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val engine = ChromiumEngine.new(VIEWPORT_W, VIEWPORT_H)
var root: BeDomNode = engine_merge_root("#1E1E1EFF")
val panel = engine_merge_panel("320px", "48px", "#2D2D2DFF")
be_dom_add_child(root, panel)

val layout: BeLayoutBox = engine.layout_dom(root)
# The outer layout box must fill the viewport width — this is
# the canonical `layout_tree` default-block behaviour.
expect(layout_get_width(layout) == VIEWPORT_W).to_be_true()
# Height must be strictly positive: the merged pipeline ran
# paint-list generation, not a stub that returns 0.
expect(layout_get_height(layout) > 0).to_be_true()
```

</details>

#### propagates a child panel into the layout tree

1. var root: BeDomNode = engine merge root
2. be dom add child


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val engine = ChromiumEngine.new(VIEWPORT_W, VIEWPORT_H)
var root: BeDomNode = engine_merge_root("#000000FF")
val panel = engine_merge_panel("120px", "24px", "#4080C0FF")
be_dom_add_child(root, panel)

# The canonical DOM must see the child we just added.
expect(be_dom_get_children(root).len() == 1).to_be_true()

val layout: BeLayoutBox = engine.layout_dom(root)
# A layout pass on a non-empty DOM produces a non-empty box
# (width > 0 AND height > 0). If either is zero, the merge
# regressed into a stub.
val lw = layout_get_width(layout)
val lh = layout_get_height(layout)
expect(lw > 0).to_be_true()
expect(lh > 0).to_be_true()
```

</details>

### Chromium engine merge — render_dom_to_scene

#### produces a RenderScene sized to the viewport

1. var root: BeDomNode = engine merge root
2. be dom add child


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val engine = ChromiumEngine.new(VIEWPORT_W, VIEWPORT_H)
var root: BeDomNode = engine_merge_root("#202020FF")
val panel = engine_merge_panel("200px", "40px", "#C04080FF")
be_dom_add_child(root, panel)

val scene: RenderScene = engine.render_dom_to_scene(root)
expect(scene.width == VIEWPORT_W).to_be_true()
expect(scene.height == VIEWPORT_H).to_be_true()
```

</details>

#### emits at least one scene command for a styled panel

1. var root: BeDomNode = engine merge root
2. be dom add child


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val engine = ChromiumEngine.new(VIEWPORT_W, VIEWPORT_H)
var root: BeDomNode = engine_merge_root("#0A0A0AFF")
val panel = engine_merge_panel("64px", "64px", "#FF8040FF")
be_dom_add_child(root, panel)

val scene: RenderScene = engine.render_dom_to_scene(root)
# A background-colored root + a background-colored child means
# the canonical paint pass must produce more than zero scene
# commands. If this drops to zero, someone swapped the engine
# for a no-op — the exact regression M4 exists to prevent.
expect(scene.commands.len() > 0).to_be_true()
```

</details>

### Chromium engine merge — canonical set_style is load-bearing

#### applies a width/height declared via be_dom_set_style

1. var node = BeDomNode element
2. be dom set style
3. be dom set style
4. be dom set style
5. be dom set style


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Use the low-level canonical setter directly — this is the
# exact code path `browser_backend.spl` uses inside the
# compositor, and proving it works from the chromium shell's
# own module closes M4's "single import graph" criterion.
var node = BeDomNode.element("div")
be_dom_set_style(node, "display", "block")
be_dom_set_style(node, "width", "256px")
be_dom_set_style(node, "height", "64px")
be_dom_set_style(node, "background-color", "#336699FF")

val engine = ChromiumEngine.new(VIEWPORT_W, VIEWPORT_H)
val layout: BeLayoutBox = engine.layout_dom(node)
expect(layout_get_width(layout) > 0).to_be_true()
expect(layout_get_height(layout) > 0).to_be_true()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui.chromium/engine_merge_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Chromium engine merge — construction
- Chromium engine merge — layout pass
- Chromium engine merge — render_dom_to_scene
- Chromium engine merge — canonical set_style is load-bearing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
