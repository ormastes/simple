# camera_spec

> Engine Camera — CameraData pure math tests

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
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# camera_spec

Engine Camera — CameraData pure math tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/camera_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Engine Camera — CameraData pure math tests

Tests camera creation, world/screen coordinate conversion,
visible bounds computation, and zoom behavior.

## Scenarios

### CameraData

<details>
<summary>Advanced: create sets zoom 1.0</summary>

#### create sets zoom 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cam = CameraData.create(800.0, 600.0)
val zoom_i = cam.zoom.value * 1000.0
expect(zoom_i).to_be_greater_than(999.0)
expect(zoom_i).to_be_less_than(1001.0)
expect(cam.is_active).to_equal(true)
```

</details>


</details>

#### world_to_screen maps camera center to viewport center

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cam = CameraData.create(800.0, 600.0)
val camera_pos = Vec2(x: 100.0, y: 200.0)
# A world point at camera center should map to viewport center (400, 300)
val screen = cam.world_to_screen(Vec2(x: 100.0, y: 200.0), camera_pos)
val sx_i = screen.x * 10.0
val sy_i = screen.y * 10.0
expect(sx_i).to_be_greater_than(3999.0)
expect(sx_i).to_be_less_than(4001.0)
expect(sy_i).to_be_greater_than(2999.0)
expect(sy_i).to_be_less_than(3001.0)
```

</details>

#### world_to_screen with offset

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cam = CameraData.create(800.0, 600.0)
val camera_pos = Vec2(x: 0.0, y: 0.0)
# World point (50, 30) with camera at origin => screen (400+50, 300+30) = (450, 330)
val screen = cam.world_to_screen(Vec2(x: 50.0, y: 30.0), camera_pos)
val sx_i = screen.x * 10.0
val sy_i = screen.y * 10.0
expect(sx_i).to_be_greater_than(4499.0)
expect(sx_i).to_be_less_than(4501.0)
expect(sy_i).to_be_greater_than(3299.0)
expect(sy_i).to_be_less_than(3301.0)
```

</details>

#### screen_to_world is inverse of world_to_screen

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cam = CameraData.create(800.0, 600.0)
val camera_pos = Vec2(x: 50.0, y: 75.0)
val original = Vec2(x: 120.0, y: 180.0)
val screen = cam.world_to_screen(original, camera_pos)
val back = cam.screen_to_world(screen, camera_pos)
val bx_i = back.x * 100.0
val by_i = back.y * 100.0
expect(bx_i).to_be_greater_than(11999.0)
expect(bx_i).to_be_less_than(12001.0)
expect(by_i).to_be_greater_than(17999.0)
expect(by_i).to_be_less_than(18001.0)
```

</details>

<details>
<summary>Advanced: visible_bounds correct at zoom 1.0</summary>

#### visible_bounds correct at zoom 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cam = CameraData.create(800.0, 600.0)
val camera_pos = Vec2(x: 400.0, y: 300.0)
val bounds = cam.visible_bounds(camera_pos)
# At zoom 1.0, visible area = viewport size centered on camera
# x = 400-400=0, y = 300-300=0, w=800, h=600
val bx_i = bounds.x * 10.0
expect(bx_i).to_be_greater_than(-1.0)
expect(bx_i).to_be_less_than(1.0)
val by_i = bounds.y * 10.0
expect(by_i).to_be_greater_than(-1.0)
expect(by_i).to_be_less_than(1.0)
val bw_i = bounds.width * 10.0
expect(bw_i).to_be_greater_than(7999.0)
expect(bw_i).to_be_less_than(8001.0)
val bh_i = bounds.height * 10.0
expect(bh_i).to_be_greater_than(5999.0)
expect(bh_i).to_be_less_than(6001.0)
```

</details>


</details>

<details>
<summary>Advanced: visible_bounds shrinks at zoom 2.0</summary>

#### visible_bounds shrinks at zoom 2.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cam = CameraData.create(800.0, 600.0)
val zoomed = cam.with_zoom(ZoomLevel(value: 2.0))
val camera_pos = Vec2(x: 400.0, y: 300.0)
val bounds = zoomed.visible_bounds(camera_pos)
# At zoom 2.0, visible area = viewport/2 = 400x300 centered on camera
# x = 400-200=200, y = 300-150=150, w=400, h=300
val bw_i = bounds.width * 10.0
expect(bw_i).to_be_greater_than(3999.0)
expect(bw_i).to_be_less_than(4001.0)
val bh_i = bounds.height * 10.0
expect(bh_i).to_be_greater_than(2999.0)
expect(bh_i).to_be_less_than(3001.0)
```

</details>


</details>

<details>
<summary>Advanced: with_zoom changes zoom and preserves viewport</summary>

#### with_zoom changes zoom and preserves viewport

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cam = CameraData.create(800.0, 600.0)
val zoomed = cam.with_zoom(ZoomLevel(value: 3.0))
val zoom_i = zoomed.zoom.value * 1000.0
expect(zoom_i).to_be_greater_than(2999.0)
expect(zoom_i).to_be_less_than(3001.0)
val vw_i = zoomed.viewport_width * 10.0
expect(vw_i).to_be_greater_than(7999.0)
expect(vw_i).to_be_less_than(8001.0)
val vh_i = zoomed.viewport_height * 10.0
expect(vh_i).to_be_greater_than(5999.0)
expect(vh_i).to_be_less_than(6001.0)
expect(zoomed.is_active).to_equal(true)
```

</details>


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
