# Component Registry Specification

> 1. var reg = ComponentRegistry

<!-- sdn-diagram:id=component_registry_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=component_registry_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

component_registry_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=component_registry_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Component Registry Specification

## Scenarios

### ComponentRegistry

#### attaches and retrieves a sprite component

1. var reg = ComponentRegistry
2. reg attach
   - Expected: components.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = ComponentRegistry(entries: {})
val nid = NodeId(raw: RawHandle(index: 0, generation: Generation(value: 1)))
val tex_id = TextureId(raw: RawHandle(index: 0, generation: Generation(value: 1)))
val src = Rect2(x: 0.0, y: 0.0, width: 32.0, height: 32.0)
val sprite_data = SpriteData(texture_id: tex_id, src_rect: src, pivot: Vec2(x: 0.5, y: 0.5), flip_x: false, flip_y: false, tint: EngineColor(r: 1.0, g: 1.0, b: 1.0, a: 1.0))
val comp = Component2D.Sprite(data: sprite_data)
reg.attach(nid, comp)
val components = reg.get_components(nid)
expect(components.len()).to_equal(1)
```

</details>

#### gets sprite data back from component

1. var reg = ComponentRegistry
2. reg attach
   - Expected: sd.src_rect.width equals `64.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = ComponentRegistry(entries: {})
val nid = NodeId(raw: RawHandle(index: 0, generation: Generation(value: 1)))
val tex_id = TextureId(raw: RawHandle(index: 0, generation: Generation(value: 1)))
val src = Rect2(x: 0.0, y: 0.0, width: 64.0, height: 64.0)
val sprite_data = SpriteData(texture_id: tex_id, src_rect: src, pivot: Vec2(x: 0.5, y: 0.5), flip_x: false, flip_y: false, tint: EngineColor(r: 1.0, g: 1.0, b: 1.0, a: 1.0))
reg.attach(nid, Component2D.Sprite(data: sprite_data))
val maybe_sprite = reg.get_sprite(nid)
if val Some(sd) = maybe_sprite:
    expect(sd.src_rect.width).to_equal(64.0)
```

</details>

#### attaches a camera component

1. var reg = ComponentRegistry
2. reg attach
   - Expected: cd.viewport_width equals `800.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = ComponentRegistry(entries: {})
val nid = NodeId(raw: RawHandle(index: 1, generation: Generation(value: 1)))
val cam = CameraData(
    zoom: 1.0,
    viewport_width: 800.0,
    viewport_height: 600.0,
    is_active: true
)
reg.attach(nid, Component2D.Camera(data: cam))
val maybe_cam = reg.get_camera(nid)
if val Some(cd) = maybe_cam:
    expect(cd.viewport_width).to_equal(800.0)
```

</details>

#### detaches all components from a node

1. var reg = ComponentRegistry
2. reg attach
3. reg detach all
   - Expected: components.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = ComponentRegistry(entries: {})
val nid = NodeId(raw: RawHandle(index: 0, generation: Generation(value: 1)))
val tex_id = TextureId(raw: RawHandle(index: 0, generation: Generation(value: 1)))
val src = Rect2(x: 0.0, y: 0.0, width: 16.0, height: 16.0)
val sprite_data = SpriteData(texture_id: tex_id, src_rect: src, pivot: Vec2(x: 0.5, y: 0.5), flip_x: false, flip_y: false, tint: EngineColor(r: 1.0, g: 1.0, b: 1.0, a: 1.0))
reg.attach(nid, Component2D.Sprite(data: sprite_data))
reg.detach_all(nid)
val components = reg.get_components(nid)
expect(components.len()).to_equal(0)
```

</details>

#### returns empty list for node with no components

1. var reg = ComponentRegistry
   - Expected: components.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = ComponentRegistry(entries: {})
val nid = NodeId(raw: RawHandle(index: 99, generation: Generation(value: 1)))
val components = reg.get_components(nid)
expect(components.len()).to_equal(0)
```

</details>

#### supports multiple components on one node

1. var reg = ComponentRegistry
2. reg attach
3. reg attach
   - Expected: components.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = ComponentRegistry(entries: {})
val nid = NodeId(raw: RawHandle(index: 0, generation: Generation(value: 1)))
val tex_id = TextureId(raw: RawHandle(index: 0, generation: Generation(value: 1)))
val src = Rect2(x: 0.0, y: 0.0, width: 32.0, height: 32.0)
val sprite_data = SpriteData(texture_id: tex_id, src_rect: src, pivot: Vec2(x: 0.5, y: 0.5), flip_x: false, flip_y: false, tint: EngineColor(r: 1.0, g: 1.0, b: 1.0, a: 1.0))
reg.attach(nid, Component2D.Sprite(data: sprite_data))
val cam = CameraData(
    zoom: 2.0,
    viewport_width: 1920.0,
    viewport_height: 1080.0,
    is_active: false
)
reg.attach(nid, Component2D.Camera(data: cam))
val components = reg.get_components(nid)
expect(components.len()).to_equal(2)
```

</details>

#### identifies component types

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tex_id = TextureId(raw: RawHandle(index: 0, generation: Generation(value: 1)))
val src = Rect2(x: 0.0, y: 0.0, width: 32.0, height: 32.0)
val sprite_data = SpriteData(texture_id: tex_id, src_rect: src, pivot: Vec2(x: 0.5, y: 0.5), flip_x: false, flip_y: false, tint: EngineColor(r: 1.0, g: 1.0, b: 1.0, a: 1.0))
val sprite_comp = Component2D.Sprite(data: sprite_data)
expect(sprite_comp.is_sprite()).to_equal(true)
expect(sprite_comp.is_camera()).to_equal(false)
expect(sprite_comp.type_name()).to_equal("Sprite")
```

</details>

#### does not leak components across node generations

1. var reg = ComponentRegistry
2. reg attach
   - Expected: reg.get_components(old_node).len() equals `1`
   - Expected: reg.get_components(new_node).len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = ComponentRegistry(entries: {})
val old_node = NodeId(raw: RawHandle(index: 7, generation: Generation(value: 1)))
val new_node = NodeId(raw: RawHandle(index: 7, generation: Generation(value: 2)))
val tex_id = TextureId(raw: RawHandle(index: 0, generation: Generation(value: 1)))
val src = Rect2(x: 0.0, y: 0.0, width: 8.0, height: 8.0)
val sprite_data = SpriteData(texture_id: tex_id, src_rect: src, pivot: Vec2(x: 0.5, y: 0.5), flip_x: false, flip_y: false, tint: EngineColor(r: 1.0, g: 1.0, b: 1.0, a: 1.0))
reg.attach(old_node, Component2D.Sprite(data: sprite_data))
expect(reg.get_components(old_node).len()).to_equal(1)
expect(reg.get_components(new_node).len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/component_registry_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ComponentRegistry

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
