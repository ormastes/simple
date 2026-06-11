# Camera Specification

> <details>

<!-- sdn-diagram:id=camera_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=camera_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

camera_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=camera_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Camera Specification

## Scenarios

### Camera2D

### create

#### stores viewport dimensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cam = Camera2D.create(0.0, 0.0, 800.0, 600.0)
expect(cam.viewport_w).to_equal(800.0)
expect(cam.viewport_h).to_equal(600.0)
```

</details>

<details>
<summary>Advanced: defaults zoom to 1.0</summary>

#### defaults zoom to 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cam = Camera2D.create(0.0, 0.0, 800.0, 600.0)
expect(cam.zoom).to_equal(1.0)
```

</details>


</details>

### world_to_screen / screen_to_world round-trip

#### round-trips the origin at identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cam = Camera2D.create(0.0, 0.0, 800.0, 600.0)
val (sx, sy) = cam.world_to_screen(0.0, 0.0)
val (wx, wy) = cam.screen_to_world(sx, sy)
expect(wx).to_equal(0.0)
expect(wy).to_equal(0.0)
```

</details>

#### maps world origin to viewport centre

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cam = Camera2D.create(0.0, 0.0, 800.0, 600.0)
val (sx, sy) = cam.world_to_screen(0.0, 0.0)
expect(sx).to_equal(400.0)
expect(sy).to_equal(300.0)
```

</details>

#### round-trips an off-centre point

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cam = Camera2D.create(0.0, 0.0, 800.0, 600.0)
val world_x = 123.0
val world_y = -45.0
val (sx, sy) = cam.world_to_screen(world_x, world_y)
val (wx, wy) = cam.screen_to_world(sx, sy)
expect(wx).to_equal(world_x)
expect(wy).to_equal(world_y)
```

</details>

### zoom

<details>
<summary>Advanced: zoom=2 doubles distance from centre</summary>

#### zoom=2 doubles distance from centre

1. var cam = Camera2D create
2. cam set zoom
   - Expected: sx1 equals `420.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cam = Camera2D.create(0.0, 0.0, 800.0, 600.0)
cam.set_zoom(2.0)
val (sx1, _) = cam.world_to_screen(10.0, 0.0)
# centre is 400; offset should be 10*2=20 so sx=420
expect(sx1).to_equal(420.0)
```

</details>


</details>

<details>
<summary>Advanced: round-trip holds at zoom=2</summary>

#### round-trip holds at zoom=2

1. var cam = Camera2D create
2. cam set zoom
   - Expected: wx equals `50.0`
   - Expected: wy equals `-30.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cam = Camera2D.create(0.0, 0.0, 800.0, 600.0)
cam.set_zoom(2.0)
val (sx, sy) = cam.world_to_screen(50.0, -30.0)
val (wx, wy) = cam.screen_to_world(sx, sy)
expect(wx).to_equal(50.0)
expect(wy).to_equal(-30.0)
```

</details>


</details>

### Rect

### create

#### stores all fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Rect.create(10.0, 20.0, 100.0, 50.0)
expect(r.x).to_equal(10.0)
expect(r.y).to_equal(20.0)
expect(r.w).to_equal(100.0)
expect(r.h).to_equal(50.0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/game2d/camera_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Camera2D
- create
- world_to_screen / screen_to_world round-trip
- zoom
- Rect
- create

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
