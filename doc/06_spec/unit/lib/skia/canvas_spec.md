# Skia Canvas Specification

Tests for SkCanvas save/restore state, dimensions, and basic predicates. Note: draw calls currently return unchanged SkCanvas values, so we only test the state-management, recording, matrix, and non-drawing methods.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SKI-006 |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/unit/lib/skia/canvas_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for SkCanvas save/restore state, dimensions, and basic predicates.
Note: draw calls currently return unchanged SkCanvas values, so we only test
the state-management, recording, matrix, and non-drawing methods.

## Scenarios

### SkCanvas construction

#### sk_canvas_make sets width and height

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = sk_canvas_make(800, 600)
expect(c.width).to_equal(800)
expect(c.height).to_equal(600)
```

</details>

#### initial save count is 1

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = sk_canvas_make(100, 100)
expect(c.get_save_count()).to_equal(1)
```

</details>

#### image_info_width matches construction

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = sk_canvas_make(1920, 1080)
expect(c.image_info_width()).to_equal(1920)
```

</details>

#### image_info_height matches construction

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = sk_canvas_make(1920, 1080)
expect(c.image_info_height()).to_equal(1080)
```

</details>

### SkCanvas save/restore

#### save increments count

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = sk_canvas_make(100, 100)
val c2 = c.save()
expect(c2.get_save_count()).to_equal(2)
```

</details>

#### save twice increments to 3

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = sk_canvas_make(100, 100)
val c3 = c.save().save()
expect(c3.get_save_count()).to_equal(3)
```

</details>

#### restore decrements count

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = sk_canvas_make(100, 100)
val c2 = c.save()
val c3 = c2.restore()
expect(c3.get_save_count()).to_equal(1)
```

</details>

#### restore at 1 stays at 1

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = sk_canvas_make(100, 100)
val c2 = c.restore()
expect(c2.get_save_count()).to_equal(1)
```

</details>

#### save_layer increments count

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = sk_canvas_make(100, 100)
val rec = sk_save_layer_rec(nil, nil)
val c2 = c.save_layer(rec)
expect(c2.get_save_count()).to_equal(2)
```

</details>

#### restore_to_count sets exact count

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = sk_canvas_make(100, 100)
val c2 = c.save().save().save()
val c3 = c2.restore_to_count(2)
expect(c3.get_save_count()).to_equal(2)
```

</details>

#### restore_to_count clamped at 1

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = sk_canvas_make(100, 100)
val c2 = c.restore_to_count(0)
expect(c2.get_save_count()).to_equal(1)
```

</details>

### SkCanvas clip bounds

#### get_device_clip_bounds returns full canvas

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = sk_canvas_make(640, 480)
val bounds = c.get_device_clip_bounds()
expect(bounds.right).to_equal(640)
expect(bounds.bottom).to_equal(480)
expect(bounds.left).to_equal(0)
expect(bounds.top).to_equal(0)
```

</details>

### SkCanvasSaveLayerRec

#### constructs with nil bounds and nil paint

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = sk_save_layer_rec(nil, nil)
expect(rec.bounds).to_equal(nil)
expect(rec.paint).to_equal(nil)
```

</details>

### SkCanvas recording

#### begin_recording preserves canvas dimensions and save count

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bounds = SkRect(left: 0.0, top: 0.0, right: 100.0, bottom: 100.0)
val c0 = sk_canvas_make(100, 100)
val c1 = c0.begin_recording(bounds)
expect(c1.width).to_equal(100)
expect(c1.height).to_equal(100)
expect(c1.get_save_count()).to_equal(1)
```

</details>

### SkCanvas matrix ops

<details>
<summary>Advanced: translate matrix exposes tx and ty for canvas transforms</summary>

#### translate matrix exposes tx and ty for canvas transforms

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Matrix3x3.translate(3.0, 4.0)
expect(m.tx()).to_equal(3.0)
expect(m.ty()).to_equal(4.0)
expect(m.scale_x()).to_equal(1.0)
expect(m.scale_y()).to_equal(1.0)
```

</details>


</details>

<details>
<summary>Advanced: set_matrix input preserves translation components</summary>

#### set_matrix input preserves translation components

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Matrix3x3.translate(11.0, 13.0)
expect(m.tx()).to_equal(11.0)
expect(m.ty()).to_equal(13.0)
expect(m.scale_x()).to_equal(1.0)
expect(m.scale_y()).to_equal(1.0)
```

</details>


</details>

<details>
<summary>Advanced: local_to_device returns identity matrix</summary>

#### local_to_device returns identity matrix

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = sk_canvas_make(100, 100)
val m = c.local_to_device()
expect(m.tx()).to_equal(0.0)
expect(m.ty()).to_equal(0.0)
expect(m.scale_x()).to_equal(1.0)
expect(m.scale_y()).to_equal(1.0)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |
