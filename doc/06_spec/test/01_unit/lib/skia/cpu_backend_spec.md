# Cpu Backend Specification

> <details>

<!-- sdn-diagram:id=cpu_backend_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cpu_backend_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cpu_backend_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cpu_backend_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cpu Backend Specification

## Scenarios

### CpuBackend.render_picture

#### empty picture produces all-zero bitmap

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pic = sk_picture_empty()
val backend = cpu_backend_new()
val cull = _cull10()
val bm = backend.render_picture(pic, cull)
val total = _pixel_sum(bm)
expect(total).to_equal(0)
```

</details>

#### DrawRect fills center pixel with the rect color

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val red = sk_color_argb(255, 200, 0, 0)
val paint = sk_paint_fill(red)
val rect = SkRect(left: 2.0, top: 2.0, right: 8.0, bottom: 8.0)
val op = sk_picture_op_draw_rect(rect, paint)
val ops = [op]
val pic = _make_picture(ops)
val backend = cpu_backend_new()
val bm = backend.render_picture(pic, _cull10())
# pixel at center (5,5) should be non-zero
val px = _pixel_at(bm, 5, 5)
val r_val = px[0] as i64
expect(r_val).to_be_greater_than(0)
```

</details>

#### DrawRRect with rx=ry=0 matches DrawRect output pixel at center

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val green = sk_color_argb(255, 0, 180, 0)
val paint = sk_paint_fill(green)
val rect = SkRect(left: 1.0, top: 1.0, right: 9.0, bottom: 9.0)
val op = sk_picture_op_draw_rrect(rect, 0.0, 0.0, paint)
val ops = [op]
val pic = _make_picture(ops)
val backend = cpu_backend_new()
val bm = backend.render_picture(pic, _cull10())
# center pixel should have the green channel non-zero
val px = _pixel_at(bm, 5, 5)
val g_val = px[1] as i64
expect(g_val).to_be_greater_than(0)
```

</details>

#### DrawPath fill op produces non-zero coverage inside the path

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blue = sk_color_argb(255, 0, 0, 200)
val paint = sk_paint_fill(blue)
# triangle: (1,1) -> (8,1) -> (4,8) -> close
val p0 = sk_path_new()
val p1 = p0.move_to(1.0, 1.0)
val p2 = p1.line_to(8.0, 1.0)
val p3 = p2.line_to(4.0, 8.0)
val path = p3.close()
val op = sk_picture_op_draw_path(path, paint)
val ops = [op]
val pic = _make_picture(ops)
val backend = cpu_backend_new()
val bm = backend.render_picture(pic, _cull10())
# pixel near centroid (4, 3) should be non-zero
val px = _pixel_at(bm, 4, 3)
val b_val = px[2] as i64
expect(b_val).to_be_greater_than(0)
```

</details>

#### DrawPath stroke op with stroke_width=1.0 produces non-zero along edges

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val white = sk_color_argb(255, 255, 255, 255)
val paint = sk_paint_stroke(white, 1.0)
# horizontal line segment across the bitmap
val p0 = sk_path_new()
val p1 = p0.move_to(1.0, 5.0)
val path = p1.line_to(9.0, 5.0)
val op = sk_picture_op_draw_path(path, paint)
val ops = [op]
val pic = _make_picture(ops)
val backend = cpu_backend_new()
val bm = backend.render_picture(pic, _cull10())
# pixel on the stroked line should be non-zero
val px = _pixel_at(bm, 5, 5)
val r_val = px[0] as i64
expect(r_val).to_be_greater_than(0)
```

</details>

#### DrawPaint fills entire bitmap with the paint color

1. rect: SkRect
   - Expected: r0 equals `255`
   - Expected: r1 equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val yellow = sk_color_argb(255, 255, 220, 0)
val paint = sk_paint_fill(yellow)
val op_paint = SkPictureOp(
    kind: SkPictureOpKind.DrawPaint,
    rect: SkRect(left: 0.0, top: 0.0, right: 0.0, bottom: 0.0),
    rx: 0.0,
    ry: 0.0,
    path: None,
    image: None,
    paint: paint,
    x: 0.0,
    y: 0.0
)
val ops = [op_paint]
val pic = _make_picture(ops)
val backend = cpu_backend_new()
val bm = backend.render_picture(pic, _cull10())
# every pixel should have its red channel set to 255
val px_corner = _pixel_at(bm, 0, 0)
val px_far = _pixel_at(bm, 9, 9)
val r0 = px_corner[0] as i64
val r1 = px_far[0] as i64
expect(r0).to_equal(255)
expect(r1).to_equal(255)
```

</details>

#### Save then Restore with DrawRect in between produces visible pixel

1. rect: SkRect
2. paint: sk paint new
3. rect: SkRect
4. paint: sk paint new


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val red = sk_color_argb(255, 220, 0, 0)
val paint = sk_paint_fill(red)
val rect = SkRect(left: 2.0, top: 2.0, right: 8.0, bottom: 8.0)
val op_save = SkPictureOp(
    kind: SkPictureOpKind.Save,
    rect: SkRect(left: 0.0, top: 0.0, right: 0.0, bottom: 0.0),
    rx: 0.0, ry: 0.0,
    path: None, image: None,
    paint: sk_paint_new(),
    x: 0.0, y: 0.0
)
val op_draw = sk_picture_op_draw_rect(rect, paint)
val op_restore = SkPictureOp(
    kind: SkPictureOpKind.Restore,
    rect: SkRect(left: 0.0, top: 0.0, right: 0.0, bottom: 0.0),
    rx: 0.0, ry: 0.0,
    path: None, image: None,
    paint: sk_paint_new(),
    x: 0.0, y: 0.0
)
val ops = [op_save, op_draw, op_restore]
val pic = _make_picture(ops)
val backend = cpu_backend_new()
val bm = backend.render_picture(pic, _cull10())
val px = _pixel_at(bm, 5, 5)
val r_val = px[0] as i64
expect(r_val).to_be_greater_than(0)
```

</details>

#### SaveLayer with half-alpha produces lower alpha than un-layered DrawRect

1. rect: SkRect
2. rect: SkRect
3. paint: sk paint new


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val red = sk_color_argb(255, 255, 0, 0)
val fill = sk_paint_fill(red)
val rect = SkRect(left: 2.0, top: 2.0, right: 8.0, bottom: 8.0)

# Reference: plain DrawRect (no layer)
val op_plain = sk_picture_op_draw_rect(rect, fill)
val pic_plain = _make_picture([op_plain])
val backend_a = cpu_backend_new()
val bm_plain = backend_a.render_picture(pic_plain, _cull10())
val px_plain = _pixel_at(bm_plain, 5, 5)
val a_plain = px_plain[3] as i64

# Layer paint with alpha=128 (half)
val half = sk_color_argb(128, 255, 255, 255)
val layer_paint = sk_paint_fill(half)
val op_savelayer = SkPictureOp(
    kind: SkPictureOpKind.SaveLayer,
    rect: SkRect(left: 0.0, top: 0.0, right: 10.0, bottom: 10.0),
    rx: 0.0, ry: 0.0,
    path: None, image: None,
    paint: layer_paint,
    x: 0.0, y: 0.0
)
val op_restore = SkPictureOp(
    kind: SkPictureOpKind.Restore,
    rect: SkRect(left: 0.0, top: 0.0, right: 0.0, bottom: 0.0),
    rx: 0.0, ry: 0.0,
    path: None, image: None,
    paint: sk_paint_new(),
    x: 0.0, y: 0.0
)
val ops_layer = [op_savelayer, op_plain, op_restore]
val pic_layer = _make_picture(ops_layer)
val backend_b = cpu_backend_new()
val bm_layer = backend_b.render_picture(pic_layer, _cull10())
val px_layer = _pixel_at(bm_layer, 5, 5)
val a_layer = px_layer[3] as i64

expect(a_layer).to_be_less_than(a_plain)
```

</details>

#### ClipRect: DrawRect inside visible, DrawRect fully outside absent

1. rect: SkRect
2. paint: sk paint new
3. SkRect
4. SkRect
   - Expected: r_out equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val white = sk_color_argb(255, 255, 255, 255)
val fill = sk_paint_fill(white)

val op_clip = SkPictureOp(
    kind: SkPictureOpKind.ClipRect,
    rect: SkRect(left: 0.0, top: 0.0, right: 5.0, bottom: 5.0),
    rx: 0.0, ry: 0.0,
    path: None, image: None,
    paint: sk_paint_new(),
    x: 0.0, y: 0.0
)
# Inside the clip
val op_inside = sk_picture_op_draw_rect(
    SkRect(left: 1.0, top: 1.0, right: 4.0, bottom: 4.0),
    fill
)
# Fully outside the clip
val op_outside = sk_picture_op_draw_rect(
    SkRect(left: 6.0, top: 6.0, right: 9.0, bottom: 9.0),
    fill
)
val ops = [op_clip, op_inside, op_outside]
val pic = _make_picture(ops)
val backend = cpu_backend_new()
val bm = backend.render_picture(pic, _cull10())

val px_in = _pixel_at(bm, 2, 2)
val r_in = px_in[0] as i64
expect(r_in).to_be_greater_than(0)

val px_out = _pixel_at(bm, 7, 7)
val r_out = px_out[0] as i64
expect(r_out).to_equal(0)
```

</details>

#### Restore beyond Save count (underflow) does not crash

1. rect: SkRect
2. paint: sk paint new
   - Expected: total equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val op_restore = SkPictureOp(
    kind: SkPictureOpKind.Restore,
    rect: SkRect(left: 0.0, top: 0.0, right: 0.0, bottom: 0.0),
    rx: 0.0, ry: 0.0,
    path: None, image: None,
    paint: sk_paint_new(),
    x: 0.0, y: 0.0
)
# Several restores with no preceding saves
val ops = [op_restore, op_restore, op_restore]
val pic = _make_picture(ops)
val backend = cpu_backend_new()
val bm = backend.render_picture(pic, _cull10())
val total = _pixel_sum(bm)
expect(total).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/skia/cpu_backend_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- CpuBackend.render_picture

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
