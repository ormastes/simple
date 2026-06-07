# Blink Image Paint Specification

> Tests the Phase B2 image-paint path: an <img> element registered on the paint walker must emit exactly one PaintOp.DrawImage entry into the PaintContext's display list, carrying the correct rect and src URL so the Canvas2D bridge can render it through the renderer-side <img> cache.

<!-- sdn-diagram:id=image_paint_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=image_paint_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

image_paint_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=image_paint_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Blink Image Paint Specification

Tests the Phase B2 image-paint path: an <img> element registered on the paint walker must emit exactly one PaintOp.DrawImage entry into the PaintContext's display list, carrying the correct rect and src URL so the Canvas2D bridge can render it through the renderer-side <img> cache.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser / Blink / Paint |
| Status | Active |
| Source | `test/01_unit/lib/blink/image_paint_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the Phase B2 image-paint path: an <img> element registered on the
paint walker must emit exactly one PaintOp.DrawImage entry into the
PaintContext's display list, carrying the correct rect and src URL so
the Canvas2D bridge can render it through the renderer-side <img>
cache.

## Scenarios

### paint walker <img> emission

#### emits a single DrawImage op for a registered <img> box

1. images push
2. pc paint box
   - Expected: count_draw_image_ops(dl) equals `1`
   - Expected: dl.ops.len().to_i64() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = make_img_layout_ctx()
val styles = [StyledBox]()
val images = [ImageEntry]()
images.push(ImageEntry(layout_id: 7, src_url: "https://example.com/x.png"))
val pc = paint_tree_new_with_images(ctx, styles, images)
pc.paint_box(7, 0.0, 0.0)
val dl = collect_display_list(pc)
expect(count_draw_image_ops(dl)).to_equal(1)
expect(dl.ops.len().to_i64()).to_equal(1)
```

</details>

#### DrawImage op carries the correct rect and URL

1. images push
2. pc paint box
   - Expected: shape_opt is None is false
   - Expected: shape.x equals `0.0`
   - Expected: shape.y equals `0.0`
   - Expected: shape.w equals `40.0`
   - Expected: shape.h equals `20.0`
   - Expected: shape.src_url equals `https://example.com/x.png`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = make_img_layout_ctx()
val styles = [StyledBox]()
val images = [ImageEntry]()
images.push(ImageEntry(layout_id: 7, src_url: "https://example.com/x.png"))
val pc = paint_tree_new_with_images(ctx, styles, images)
pc.paint_box(7, 0.0, 0.0)
val dl = collect_display_list(pc)
val shape_opt = first_draw_image_shape(dl)
expect(shape_opt is None).to_equal(false)
if val shape = shape_opt:
    expect(shape.x).to_equal(0.0)
    expect(shape.y).to_equal(0.0)
    expect(shape.w).to_equal(40.0)
    expect(shape.h).to_equal(20.0)
    expect(shape.src_url).to_equal("https://example.com/x.png")
```

</details>

#### layout boxes without an ImageEntry emit no DrawImage op

1. pc paint box
   - Expected: count_draw_image_ops(dl) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = make_img_layout_ctx()
val styles = [StyledBox]()
val pc = paint_tree_new_with_images(ctx, styles, [ImageEntry]())
pc.paint_box(7, 0.0, 0.0)
val dl = collect_display_list(pc)
expect(count_draw_image_ops(dl)).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
