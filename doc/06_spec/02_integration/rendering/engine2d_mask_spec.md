# Engine2d Mask Specification

> 1. var engine = Engine2D create with backend

<!-- sdn-diagram:id=engine2d_mask_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=engine2d_mask_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

engine2d_mask_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=engine2d_mask_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2d Mask Specification

## Scenarios

### Engine2D Stencil Mask

#### cpu backend

#### set_mask blocks draws in masked region

1. var engine = Engine2D create with backend
2. engine clear
3. engine set mask
4. engine draw rect filled
   - Expected: color_r(p_left) equals `0`
   - Expected: color_r(p_right) equals `255`
   - Expected: color_g(p_right) equals `0`
5. engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine2D.create_with_backend(10, 10, "cpu")
engine.clear(rgb(0, 0, 0))

val mask = _make_right_half_mask()
engine.set_mask(mask, 10, 10)
engine.draw_rect_filled(0, 0, 10, 10, rgb(255, 0, 0))

val pixels = engine.read_pixels()
val p_left = pixels[0 * 10 + 2]
expect(color_r(p_left)).to_equal(0)
val p_right = pixels[0 * 10 + 7]
expect(color_r(p_right)).to_equal(255)
expect(color_g(p_right)).to_equal(0)
engine.shutdown()
```

</details>

#### clear_mask removes clipping

1. var engine = Engine2D create with backend
2. engine clear
3. engine set mask
4. engine draw rect filled
   - Expected: color_r(p1) equals `0`
5. engine clear mask
6. engine draw rect filled
   - Expected: color_g(p2) equals `255`
7. engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine2D.create_with_backend(10, 10, "cpu")
engine.clear(rgb(0, 0, 0))

val mask = _make_block_all_mask()
engine.set_mask(mask, 10, 10)
engine.draw_rect_filled(0, 0, 10, 10, rgb(255, 0, 0))

val p1 = engine.read_pixels()[55]
expect(color_r(p1)).to_equal(0)

engine.clear_mask()
engine.draw_rect_filled(0, 0, 10, 10, rgb(0, 255, 0))

val p2 = engine.read_pixels()[55]
expect(color_g(p2)).to_equal(255)
engine.shutdown()
```

</details>

#### mask does not affect clear

1. var engine = Engine2D create with backend
2. engine clear
3. engine set mask
4. engine clear
   - Expected: color_b(p) equals `255`
5. engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine2D.create_with_backend(10, 10, "cpu")
engine.clear(rgb(255, 0, 0))

val mask = _make_block_all_mask()
engine.set_mask(mask, 10, 10)

engine.clear(rgb(0, 0, 255))
val pixels = engine.read_pixels()
val p = pixels[0]
expect(color_b(p)).to_equal(255)
engine.shutdown()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/engine2d_mask_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Engine2D Stencil Mask

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
