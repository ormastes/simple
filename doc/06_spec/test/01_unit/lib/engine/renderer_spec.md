# renderer_spec

> Engine Renderer — SoftwareRenderer & RenderCommandBuffer Tests

<!-- sdn-diagram:id=renderer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=renderer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

renderer_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=renderer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# renderer_spec

Engine Renderer — SoftwareRenderer & RenderCommandBuffer Tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/renderer_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Engine Renderer — SoftwareRenderer & RenderCommandBuffer Tests

Tests renderer creation, clear, draw commands, and render stats.

## Scenarios

### SoftwareRenderer

#### creates with correct dimensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val renderer = SoftwareRenderer.create(4, 3)
expect(renderer.width).to_equal(4)
expect(renderer.height).to_equal(3)
```

</details>

#### has correct pixel buffer size

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val renderer = SoftwareRenderer.create(3, 3)
expect(renderer.pixels.len()).to_equal(9)
```

</details>

#### starts with zero draw stats

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val renderer = SoftwareRenderer.create(4, 4)
expect(renderer.stats.draw_calls).to_equal(0)
expect(renderer.stats.triangles).to_equal(0)
expect(renderer.stats.vertices).to_equal(0)
```

</details>

#### clears the pixel buffer

1. var renderer = SoftwareRenderer create
2. renderer clear
   - Expected: first_pixel equals `last_pixel`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var renderer = SoftwareRenderer.create(4, 4)
renderer.clear()
# After clear, all pixels should be set to clear_color (black by default)
# Black packed = 0x000000FF = 255
val first_pixel = renderer.pixels[0]
val last_pixel = renderer.pixels[15]
# Both should be the same (uniform clear)
expect(first_pixel).to_equal(last_pixel)
```

</details>

#### renders a DrawRect command and tracks stats

1. var renderer = SoftwareRenderer create
2. var buf = RenderCommandBuffer create
3. buf push
   - Expected: stats.draw_calls equals `1`
   - Expected: stats.triangles equals `2`
   - Expected: stats.vertices equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var renderer = SoftwareRenderer.create(8, 8)
var buf = RenderCommandBuffer.create()
val rect = Rect2.new(1.0, 1.0, 3.0, 3.0)
buf.push(RenderCommand.DrawRect(rect: rect, color: EngineColor.red(), z_order: ZIndex(value: 0)))
val stats = renderer.render_frame(buf)
expect(stats.draw_calls).to_equal(1)
expect(stats.triangles).to_equal(2)
expect(stats.vertices).to_equal(4)
```

</details>

### RenderCommandBuffer

#### starts empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = RenderCommandBuffer.create()
expect(buf.len()).to_equal(0)
```

</details>

#### pushes commands and tracks length

1. var buf = RenderCommandBuffer create
2. buf push
3. rect: Rect2 new
4. color: EngineColor white
5. z order: ZIndex
   - Expected: buf.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf = RenderCommandBuffer.create()
buf.push(RenderCommand.Clear(color: EngineColor.black()))
buf.push(RenderCommand.DrawRect(
    rect: Rect2.new(0.0, 0.0, 10.0, 10.0),
    color: EngineColor.white(),
    z_order: ZIndex(value: 0)
))
expect(buf.len()).to_equal(2)
```

</details>

#### clears all commands

1. var buf = RenderCommandBuffer create
2. buf push
3. buf push
4. buf clear
   - Expected: buf.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf = RenderCommandBuffer.create()
buf.push(RenderCommand.Clear(color: EngineColor.blue()))
buf.push(RenderCommand.Clear(color: EngineColor.red()))
buf.clear()
expect(buf.len()).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
