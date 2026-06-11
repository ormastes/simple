# Scene To Canvas2d Json Specification

> 1. scene fill rect

<!-- sdn-diagram:id=scene_to_canvas2d_json_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scene_to_canvas2d_json_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scene_to_canvas2d_json_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scene_to_canvas2d_json_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scene To Canvas2d Json Specification

## Scenarios

### render_scene_to_canvas2d_ops

#### serializes basic scene commands for the hosted canvas shell

1. scene fill rect
2. scene text
3. scene clip push
4. scene clip pop


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = render_scene(
    [
        scene_fill_rect(4, 6, 20, 12, 0xFFFF0000),
        scene_text(10, 24, "Hello", 0xFF112233, 14),
        scene_clip_push(0, 0, 40, 30),
        scene_clip_pop()
    ],
    80,
    60
)

val json = render_scene_to_canvas2d_ops(scene)
expect(json).to_contain("\"op\":\"fillRect\"")
expect(json).to_contain("\"text\":\"Hello\"")
expect(json).to_contain("\"op\":\"pushClip\"")
expect(json).to_contain("\"op\":\"popClip\"")
```

</details>

#### applies offsets when translating scene output

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = render_scene([scene_fill_rect(2, 3, 8, 9, 0xFF00FF00)], 32, 24)
val json = render_scene_to_canvas2d_ops_with_offset(scene, 10, 20)

expect(json).to_contain("\"x\":12")
expect(json).to_contain("\"y\":23")
```

</details>

#### serializes primitive placement and high-dpi scale for mobile canvas shells

1. scene stroke rect
2. scene line
3. scene circle filled
4. scene rounded rect
5. scene gradient rect


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = render_scene(
    [
        scene_stroke_rect(1, 2, 10, 11, 0xFF010203, 2),
        scene_line(3, 4, 13, 14, 0xFF102030, 1),
        scene_circle_filled(5, 6, 7, 0xFFABCDEF),
        scene_rounded_rect(8, 9, 20, 21, 0xFF445566, 4),
        scene_gradient_rect(10, 12, 30, 40, 0xFF000000, 0xFFFFFFFF)
    ],
    100,
    50
)

val json = render_scene_to_canvas2d_ops_with_offset_and_scale(scene, 1, 2, 2)
expect(json).to_contain("\"width\":200")
expect(json).to_contain("\"height\":100")
expect(json).to_contain("\"devicePixelRatio\":2")
expect(json).to_contain("\"op\":\"strokeRect\"")
expect(json).to_contain("\"strokeWidth\":4")
expect(json).to_contain("\"op\":\"line\"")
expect(json).to_contain("\"x2\":28")
expect(json).to_contain("\"op\":\"circle\"")
expect(json).to_contain("\"filled\":true")
expect(json).to_contain("\"op\":\"roundRect\"")
expect(json).to_contain("\"radius\":8")
expect(json).to_contain("\"op\":\"linearGradientRect\"")
```

</details>

#### serializes image bounds and escapes text content

1. scene text
2. scene image


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = render_scene(
    [
        scene_text(1, 2, "Hello \"Canvas\"\nWorld", 0xFF222222, 16),
        scene_image(4, 5, 20, 10, [0xFF000000, 0xFFFFFFFF], 2, 1)
    ],
    64,
    32
)

val json = render_scene_to_canvas2d_ops(scene)
expect(json).to_contain("Hello \\\"Canvas\\\"\\nWorld")
expect(json).to_contain("\"op\":\"drawImage\"")
expect(json).to_contain("\"pixelWidth\":2")
expect(json).to_contain("\"pixelHeight\":1")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/render_scene/scene_to_canvas2d_json_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- render_scene_to_canvas2d_ops

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
