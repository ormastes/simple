# Skia Picture Specification

> Tests for SkPicture and SkPictureRecorder construction and state.

<!-- sdn-diagram:id=picture_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=picture_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

picture_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=picture_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skia Picture Specification

Tests for SkPicture and SkPictureRecorder construction and state.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SKI-007 |
| Category | Stdlib |
| Difficulty | 1/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/skia/picture_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for SkPicture and SkPictureRecorder construction and state.

## Scenarios

### SkPicture

#### sk_picture_empty creates zero op picture

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pic = sk_picture_empty()
expect(pic.approximate_op_count()).to_equal(0)
```

</details>

#### empty picture cull_rect is zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pic = sk_picture_empty()
val cr = pic.cull_rect()
expect(cr.left).to_equal(0.0)
expect(cr.right).to_equal(0.0)
```

</details>

### SkPictureRecorder

#### new recorder is not recording

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = sk_picture_recorder_new()
expect(rec.is_recording()).to_equal(false)
```

</details>

#### begin_recording sets recording flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = sk_picture_recorder_new()
val bounds = sk_rect_make_wh(800.0, 600.0)
val rec2 = rec.begin_recording(bounds)
expect(rec2.is_recording()).to_equal(true)
```

</details>

#### begin_recording stores bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = sk_picture_recorder_new()
val bounds = sk_rect_make_wh(800.0, 600.0)
val rec2 = rec.begin_recording(bounds)
expect(rec2.cull_rect.right).to_equal(800.0)
expect(rec2.cull_rect.bottom).to_equal(600.0)
```

</details>

#### finish_recording returns a picture

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = sk_picture_recorder_new()
val bounds = sk_rect_make_wh(200.0, 200.0)
val rec2 = rec.begin_recording(bounds)
val pic = rec2.finish_recording()
expect(pic.approximate_op_count()).to_equal(0)
```

</details>

#### finished picture preserves cull_rect

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = sk_picture_recorder_new()
val bounds = sk_rect_make_wh(500.0, 300.0)
val pic = rec.begin_recording(bounds).finish_recording()
val cr = pic.cull_rect()
expect(cr.right).to_equal(500.0)
expect(cr.bottom).to_equal(300.0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
