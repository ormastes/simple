# Engine2d Drawing Specification

> 1. var engine = Engine2D create with backend

<!-- sdn-diagram:id=engine2d_drawing_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=engine2d_drawing_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

engine2d_drawing_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=engine2d_drawing_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2d Drawing Specification

## Scenarios

### Engine2D Drawing Primitives

#### cpu backend

#### draw_rect_filled fills correct region

1. var engine = Engine2D create with backend

2. engine clear

3. engine draw rect filled
   - Expected: color_r(inside) equals `255`
   - Expected: color_g(inside) equals `0`
   - Expected: color_r(outside) equals `0`

4. engine shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine2D.create_with_backend(10, 10, "cpu")
engine.clear(rgb(0, 0, 0))
engine.draw_rect_filled(2, 2, 3, 3, rgb(255, 0, 0))
val pixels = engine.read_pixels()
val inside = pixels[3 * 10 + 3]
expect(color_r(inside)).to_equal(255)
expect(color_g(inside)).to_equal(0)
val outside = pixels[0 * 10 + 0]
expect(color_r(outside)).to_equal(0)
engine.shutdown()
```

</details>

#### clear fills entire framebuffer

1. var engine = Engine2D create with backend

2. engine clear
   - Expected: color_r(tl) equals `255`
   - Expected: color_g(tl) equals `0`
   - Expected: color_r(br) equals `255`

3. engine shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine2D.create_with_backend(8, 8, "cpu")
engine.clear(rgb(255, 0, 0))
val pixels = engine.read_pixels()
val tl = pixels[0 * 8 + 0]
expect(color_r(tl)).to_equal(255)
expect(color_g(tl)).to_equal(0)
val br = pixels[7 * 8 + 7]
expect(color_r(br)).to_equal(255)
engine.shutdown()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/engine2d_drawing_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Engine2D Drawing Primitives

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
