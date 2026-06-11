# Paint Image Scene Specification

> <details>

<!-- sdn-diagram:id=paint_image_scene_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=paint_image_scene_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

paint_image_scene_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=paint_image_scene_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Paint Image Scene Specification

## Scenarios

### Browser Paint Image Scene Bridge

#### converts image paint commands into scene image commands

- PaintCommand image
   - Expected: scene.commands.len() equals `1`
   - Expected: scene.commands[0].kind equals `image`
   - Expected: scene.commands[0].x equals `4`
   - Expected: scene.commands[0].y equals `6`
   - Expected: scene.commands[0].width equals `20`
   - Expected: scene.commands[0].height equals `10`
   - Expected: scene.commands[0].pixel_width equals `2`
   - Expected: scene.commands[0].pixel_height equals `2`
   - Expected: scene.commands[0].pixels.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = [0xFFFF0000u32, 0xFF00FF00u32, 0xFF0000FFu32, 0xFFFFFFFFu32]
val scene = paint_commands_to_scene([
    PaintCommand.image(4, 6, 20, 10, pixels, 2, 2)
], 64, 64)
expect(scene.commands.len()).to_equal(1)
expect(scene.commands[0].kind).to_equal("image")
expect(scene.commands[0].x).to_equal(4)
expect(scene.commands[0].y).to_equal(6)
expect(scene.commands[0].width).to_equal(20)
expect(scene.commands[0].height).to_equal(10)
expect(scene.commands[0].pixel_width).to_equal(2)
expect(scene.commands[0].pixel_height).to_equal(2)
expect(scene.commands[0].pixels.len()).to_equal(4)
```

</details>

#### skips image paint commands without source pixels

- PaintCommand image
   - Expected: scene.commands.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = paint_commands_to_scene([
    PaintCommand.image(4, 6, 20, 10, [], 0, 0)
], 64, 64)
expect(scene.commands.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/paint_image_scene_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Browser Paint Image Scene Bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
