# Blink PaintTreeWalker Specification

> Tests for paint_tree_walker: PaintContext creation, style lookup, background fill emission, transparent-background suppression, and full two-box walk. Mirrors Blink's BlockPainter / BoxPainter block-box paint pass.

<!-- sdn-diagram:id=paint_tree_walker_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=paint_tree_walker_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

paint_tree_walker_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=paint_tree_walker_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Blink PaintTreeWalker Specification

Tests for paint_tree_walker: PaintContext creation, style lookup, background fill emission, transparent-background suppression, and full two-box walk. Mirrors Blink's BlockPainter / BoxPainter block-box paint pass.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser / Blink / Paint |
| Status | Active |
| Source | `test/01_unit/lib/blink/paint_tree_walker_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for paint_tree_walker: PaintContext creation, style lookup, background
fill emission, transparent-background suppression, and full two-box walk.
Mirrors Blink's BlockPainter / BoxPainter block-box paint pass.

## Scenarios

### paint_tree_new

#### creates PaintContext with recorder-attached canvas

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = make_ctx_800x600()
val styles = [StyledBox]()
val pc = paint_tree_new(ctx, styles)
# Canvas must have a recorder attached — verified by checking width/height
# match the viewport and that end_recording yields a valid SkPicture.
expect(pc.canvas.width).to_equal(800)
expect(pc.canvas.height).to_equal(600)
val pic = finalize_paint(pc)
# A freshly started recording with no draw calls has 0 ops.
expect(pic.op_count).to_equal(0)
```

</details>

### find_style

#### missing layout_id returns None

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = make_ctx_800x600()
val styles = [StyledBox]()
val pc = paint_tree_new(ctx, styles)
val result = pc.find_style(99)
expect(result is None).to_equal(true)
```

</details>

#### present layout_id returns Some

1. styles push
   - Expected: result is None is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = make_ctx_800x600()
val sb = StyledBox(layout_id: 42, style: make_opaque_style())
val styles = [StyledBox]()
styles.push(sb)
val pc = paint_tree_new(ctx, styles)
val result = pc.find_style(42)
expect(result is None).to_equal(false)
```

</details>

### paint_box

#### background color with a>0 emits a DrawRect op in the canvas' recorder

1. styles push
2. pc paint box


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = make_single_box_ctx()
val sb = StyledBox(layout_id: 1, style: make_opaque_style())
val styles = [StyledBox]()
styles.push(sb)
val pc = paint_tree_new(ctx, styles)
pc.paint_box(1, 0.0, 0.0)
val pic = finalize_paint(pc)
# One DrawRect op expected for the opaque background fill.
expect(pic.op_count).to_be_greater_than(0)
```

</details>

#### transparent background (a=0) emits no ops

1. styles push
2. pc paint box
   - Expected: pic.op_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = make_single_box_ctx()
val sb = StyledBox(layout_id: 1, style: make_transparent_style())
val styles = [StyledBox]()
styles.push(sb)
val pc = paint_tree_new(ctx, styles)
pc.paint_box(1, 0.0, 0.0)
val pic = finalize_paint(pc)
# Transparent background must produce zero ops.
expect(pic.op_count).to_equal(0)
```

</details>

### paint_tree

#### full walk of 2 boxes emits 2 DrawRect ops (parent + child)

1. styles push
2. styles push
   - Expected: pic.op_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = make_two_box_ctx()
val sb_parent = StyledBox(layout_id: 10, style: make_opaque_style())
val sb_child  = StyledBox(layout_id: 11, style: make_opaque_style())
val styles = [StyledBox]()
styles.push(sb_parent)
styles.push(sb_child)
val pic = paint_tree(ctx, styles)
# Exactly 2 DrawRect ops: one for parent background, one for child.
expect(pic.op_count).to_equal(2)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
