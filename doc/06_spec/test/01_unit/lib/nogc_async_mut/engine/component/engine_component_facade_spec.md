# Engine Component Facade Specification

> 1. src rect: Rect2

<!-- sdn-diagram:id=engine_component_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=engine_component_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

engine_component_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=engine_component_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine Component Facade Specification

## Scenarios

### nogc_async_mut engine component facade

#### re-exports 2D registry and helper extensions

1. src rect: Rect2
2. pivot: Vec2
3. tint: EngineColor
   - Expected: reg.get_components(node).len() equals `0`
   - Expected: sprite_component.is_sprite() is true
   - Expected: sprite_component.type_name() equals `Sprite`
   - Expected: screen.x equals `400.0`
   - Expected: tilemap.get_tile(TileCoord(col: 1, row: 1)).value equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = NodeId(raw: RawHandle(index: 1, generation: Generation(value: 1)))
val tex = TextureId(raw: RawHandle(index: 2, generation: Generation(value: 1)))
val sprite = SpriteData(
    texture_id: tex,
    src_rect: Rect2(x: 0.0, y: 0.0, width: 16.0, height: 16.0),
    pivot: Vec2(x: 0.5, y: 0.5),
    flip_x: false,
    flip_y: false,
    tint: EngineColor(r: 1.0, g: 1.0, b: 1.0, a: 1.0)
)
val reg = ComponentRegistry.create()
expect(reg.get_components(node).len()).to_equal(0)
val sprite_component = Component2D.Sprite(data: sprite)
expect(sprite_component.is_sprite()).to_equal(true)
expect(sprite_component.type_name()).to_equal("Sprite")

val cam = CameraData.create(800.0, 600.0)
val screen = cam.world_to_screen(Vec2(x: 0.0, y: 0.0), Vec2.zero())
expect(screen.x).to_equal(400.0)

val tilemap = TileMapData.create(tex, 16, 16, 4, 4).set_tile(TileCoord(col: 1, row: 1), TileIndex(value: 7))
expect(tilemap.get_tile(TileCoord(col: 1, row: 1)).value).to_equal(7)
```

</details>

#### re-exports mesh and 3D registry surfaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cube = create_cube(2.0)
expect(cube.vertex_count()).to_equal(24)
val reg3d = ComponentRegistry3D.create()
expect(reg3d.entries.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/engine/component/engine_component_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut engine component facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
