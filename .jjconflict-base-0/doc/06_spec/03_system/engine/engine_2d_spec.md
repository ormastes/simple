# Simple-Native 2D Game Engine — Current API Smoke Specification

> 1. var store = NodeStore new

<!-- sdn-diagram:id=engine_2d_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=engine_2d_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

engine_2d_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=engine_2d_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple-Native 2D Game Engine — Current API Smoke Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/engine/engine_2d_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### Engine2D current API smoke

#### creates scene nodes with valid generational handles

1. var store = NodeStore new
   - Expected: root.is_valid() is true
   - Expected: child.is_valid() is true
   - Expected: store.count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NodeStore.new()
val root = store.create_node("root")
val child = store.create_node("child")
expect(root.is_valid()).to_equal(true)
expect(child.is_valid()).to_equal(true)
expect(store.count).to_equal(2)
```

</details>

#### constructs camera components through Component2D

1. var registry = ComponentRegistry create
2. registry attach
   - Expected: cam.viewport_width equals `800.0`
   - Expected: cam.is_active is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = NodeId(raw: RawHandle.new(0, 1))
var registry = ComponentRegistry.create()
val cam = CameraData.create(800.0, 600.0)
registry.attach(node, Component2D.Camera(data: cam))
expect(cam.viewport_width).to_equal(800.0)
expect(cam.is_active).to_equal(true)
```

</details>

#### renders command buffers through the software renderer

1. var renderer = SoftwareRenderer create
2. var buf = RenderCommandBuffer create
3. buf push
4. rect: Rect2
5. color: EngineColor red
6. z order: ZIndex
   - Expected: buf.len() equals `2`
   - Expected: renderer.get_pixels().len() equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var renderer = SoftwareRenderer.create(4, 3)
var buf = RenderCommandBuffer.create()
buf.push(RenderCommand.Clear(color: EngineColor.black()))
buf.push(RenderCommand.DrawRect(
    rect: Rect2(x: 0.0, y: 0.0, width: 2.0, height: 2.0),
    color: EngineColor.red(),
    z_order: ZIndex(value: 0)))
val stats = renderer.render_frame(buf)
expect(buf.len()).to_equal(2)
expect(stats.draw_calls).to_be_greater_than(0)
expect(renderer.get_pixels().len()).to_equal(12)
```

</details>

#### binds input actions with the current KeyCode field

1. var mgr = InputManager create
2. mgr bind key action
   - Expected: mgr.is_action_pressed("jump") is false
   - Expected: mgr.get_action_strength("jump") equals `0.0`
3. mgr destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = InputManager.create(0)
mgr.bind_key_action("jump", KeyCode(code: 32))
expect(mgr.is_action_pressed("jump")).to_equal(false)
expect(mgr.get_action_strength("jump")).to_equal(0.0)
mgr.destroy()
```

</details>

#### creates texture, atlas, sprite sheet, and tilemap resources

1. var store = TextureStore new
   - Expected: tex_id.is_valid() is true
2. var atlas = TextureAtlas create
   - Expected: region == nil is false
   - Expected: atlas.region_count() equals `1`
   - Expected: sheet.columns equals `4`
   - Expected: sheet.rows equals `4`
3. var tm = TileMapData create
4. tm = tm set tile
   - Expected: tm.get_tile(TileCoord(col: 0, row: 0)).value equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = TextureStore.new()
val tex_id = store.add(Texture.create(128, 128))
expect(tex_id.is_valid()).to_equal(true)

var atlas = TextureAtlas.create(256, 256)
val pixels: [i64] = [0xFFFFFFFF]
val region = atlas.pack(1, 1, pixels)
expect(region == nil).to_equal(false)
expect(atlas.region_count()).to_equal(1)

val sheet = SpriteSheet.create(tex_id, 32, 32, 4, 4)
expect(sheet.columns).to_equal(4)
expect(sheet.rows).to_equal(4)

var tm = TileMapData.create(tex_id, 16, 16, 4, 4)
tm = tm.set_tile(TileCoord(col: 0, row: 0), TileIndex(value: 5))
expect(tm.get_tile(TileCoord(col: 0, row: 0)).value).to_equal(5)
```

</details>

#### tracks signal registrations and vector render commands

1. var sig = Signal create
   - Expected: sig.connection_count() equals `1`
   - Expected: sig.is_connected(conn) is true
2. var bus = EventBus create
3. bus register
   - Expected: bus.has_signal("on_hit") is true
4. var cmds = RenderCommandBuffer create
5. vector fill rect
   - Expected: cmds.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sig = Signal.create("test")
val conn = sig.connect(&:len)
expect(sig.connection_count()).to_equal(1)
expect(sig.is_connected(conn)).to_equal(true)

var bus = EventBus.create()
bus.register("on_hit")
expect(bus.has_signal("on_hit")).to_equal(true)

val vector = VectorRenderer.create()
var cmds = RenderCommandBuffer.create()
vector.fill_rect(cmds, Rect2(x: 1.0, y: 1.0, width: 2.0, height: 2.0), EngineColor.white(), ZIndex(value: 1))
expect(cmds.len()).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
