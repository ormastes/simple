# Draw Quad Specification

> <details>

<!-- sdn-diagram:id=draw_quad_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=draw_quad_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

draw_quad_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=draw_quad_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Draw Quad Specification

## Scenarios

### SharedQuadState

#### opacity is 1.0 when built with explicit value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sqs = _identity_sqs()
expect sqs.opacity to_equal 1.0
```

</details>

#### is_clipped defaults to false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sqs = _identity_sqs()
expect sqs.is_clipped to_equal false
```

</details>

### DrawQuad::solid_color

#### sets kind to SolidColor

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rect = _rect(0.0, 0.0, 50.0, 50.0)
val color = SkColor4f(r: 1.0, g: 0.0, b: 0.0, a: 1.0)
val q = DrawQuad.solid_color(0, rect, color)
val is_solid = match q.kind:
    DrawQuadKind.SolidColor: true
    _: false
expect is_solid to_equal true
```

</details>

#### carries the supplied color

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rect = _rect(0.0, 0.0, 50.0, 50.0)
val color = SkColor4f(r: 0.5, g: 0.2, b: 0.8, a: 1.0)
val q = DrawQuad.solid_color(0, rect, color)
expect q.solid_color.r to_equal 0.5
expect q.solid_color.g to_equal 0.2
```

</details>

#### rect and visible_rect are both set to constructor rect

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rect = _rect(10.0, 20.0, 60.0, 80.0)
val color = SkColor4f(r: 0.0, g: 0.0, b: 0.0, a: 1.0)
val q = DrawQuad.solid_color(2, rect, color)
expect q.rect.left to_equal 10.0
expect q.visible_rect.top to_equal 20.0
```

</details>

### DrawQuad::texture

#### sets kind to Texture

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rect = _rect(0.0, 0.0, 100.0, 100.0)
val mailbox = SharedImageMailbox(bytes: [])
val q = DrawQuad.texture(0, rect, mailbox)
val is_tex = match q.kind:
    DrawQuadKind.Texture: true
    _: false
expect is_tex to_equal true
```

</details>

#### carries the mailbox

1. expect q texture mailbox bytes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rect = _rect(0.0, 0.0, 100.0, 100.0)
val mailbox = SharedImageMailbox(bytes: [1, 2, 3])
val q = DrawQuad.texture(0, rect, mailbox)
expect q.texture_mailbox.bytes.len() to_equal 3
```

</details>

### DrawQuad::render_pass

#### sets kind to RenderPass

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rect = _rect(0.0, 0.0, 800.0, 600.0)
val q = DrawQuad.render_pass(0, rect, 42)
val is_rp = match q.kind:
    DrawQuadKind.RenderPass: true
    _: false
expect is_rp to_equal true
```

</details>

#### carries the pass_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rect = _rect(0.0, 0.0, 800.0, 600.0)
val q = DrawQuad.render_pass(1, rect, 99)
expect q.render_pass_id to_equal 99
```

</details>

### DrawQuadKind

#### has 6 variants distinguishable by pattern match

1. expect kinds len


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kinds: [DrawQuadKind] = [
    DrawQuadKind.SolidColor,
    DrawQuadKind.Texture,
    DrawQuadKind.Tile,
    DrawQuadKind.RenderPass,
    DrawQuadKind.Video,
    DrawQuadKind.Debug
]
expect kinds.len() to_equal 6
```

</details>

#### two quads with same sqs_index have distinct rects

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r1 = _rect(0.0, 0.0, 10.0, 10.0)
val r2 = _rect(20.0, 20.0, 30.0, 30.0)
val color = SkColor4f(r: 0.0, g: 0.0, b: 0.0, a: 1.0)
val q1 = DrawQuad.solid_color(0, r1, color)
val q2 = DrawQuad.solid_color(0, r2, color)
expect q1.rect.left to_equal 0.0
expect q2.rect.left to_equal 20.0
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/viz/draw_quad_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SharedQuadState
- DrawQuad::solid_color
- DrawQuad::texture
- DrawQuad::render_pass
- DrawQuadKind

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
