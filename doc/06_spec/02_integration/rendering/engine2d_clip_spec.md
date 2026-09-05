# Engine2d Clip Specification

> 1. var engine = Engine2D create with backend

<!-- sdn-diagram:id=engine2d_clip_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=engine2d_clip_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

engine2d_clip_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=engine2d_clip_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2d Clip Specification

## Scenarios

### Engine2D Clipping

#### cpu backend

#### set_clip restricts draw_rect_filled

1. var engine = Engine2D create with backend
2. engine clear
3. engine set clip
4. engine draw rect filled
   - Expected: color_r(outside) equals `0`
   - Expected: color_r(inside) equals `255`
5. engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine2D.create_with_backend(10, 10, "cpu")
engine.clear(rgb(0, 0, 0))
engine.set_clip(5, 5, 5, 5)
engine.draw_rect_filled(0, 0, 10, 10, rgb(255, 0, 0))
val pixels = engine.read_pixels()
val outside = pixels[2 * 10 + 2]
expect(color_r(outside)).to_equal(0)
val inside = pixels[7 * 10 + 7]
expect(color_r(inside)).to_equal(255)
engine.shutdown()
```

</details>

#### clear_clip restores full drawing area

1. var engine = Engine2D create with backend
2. engine clear
3. engine set clip
4. engine clear clip
5. engine draw rect filled
   - Expected: color_g(p) equals `255`
6. engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine2D.create_with_backend(10, 10, "cpu")
engine.clear(rgb(0, 0, 0))
engine.set_clip(5, 5, 5, 5)
engine.clear_clip()
engine.draw_rect_filled(0, 0, 10, 10, rgb(0, 255, 0))
val pixels = engine.read_pixels()
val p = pixels[2 * 10 + 2]
expect(color_g(p)).to_equal(255)
engine.shutdown()
```

</details>

#### clip does not affect clear

1. var engine = Engine2D create with backend
2. engine set clip
3. engine clear
   - Expected: color_b(p) equals `255`
4. engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine2D.create_with_backend(10, 10, "cpu")
engine.set_clip(5, 5, 5, 5)
engine.clear(rgb(0, 0, 255))
val pixels = engine.read_pixels()
val p = pixels[2 * 10 + 2]
expect(color_b(p)).to_equal(255)
engine.shutdown()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/engine2d_clip_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Engine2D Clipping

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
