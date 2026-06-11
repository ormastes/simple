# command_spec

> Engine RenderCommand & RenderCommandBuffer Tests

<!-- sdn-diagram:id=command_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=command_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

command_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=command_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# command_spec

Engine RenderCommand & RenderCommandBuffer Tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/command_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Engine RenderCommand & RenderCommandBuffer Tests

Tests enum variant construction, buffer creation, and push/clear operations.

## Scenarios

### RenderCommand

### Clear

#### constructs with a color

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = RenderCommand.Clear(color: EngineColor.black())
# If we get here without error, construction succeeded
expect(1).to_equal(1)
```

</details>

#### constructs with a non-black color

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = RenderCommand.Clear(color: EngineColor.red())
expect(1).to_equal(1)
```

</details>

### DrawRect

#### constructs with Rect2, EngineColor, and ZIndex

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rect = Rect2.new(10.0, 20.0, 100.0, 50.0)
val color = EngineColor.red()
val z = ZIndex(value: 5)
val cmd = RenderCommand.DrawRect(rect: rect, color: color, z_order: z)
expect(1).to_equal(1)
```

</details>

#### constructs with zero z_order

1. color: EngineColor white
2. z order: ZIndex
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rect = Rect2.new(0.0, 0.0, 1.0, 1.0)
val cmd = RenderCommand.DrawRect(
    rect: rect,
    color: EngineColor.white(),
    z_order: ZIndex(value: 0)
)
expect(1).to_equal(1)
```

</details>

### DrawCircle

#### constructs with center, radius, color, and z_order

1. color: EngineColor green
2. z order: ZIndex
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = RenderCommand.DrawCircle(
    cx: 50.0,
    cy: 60.0,
    radius: 25.0,
    color: EngineColor.green(),
    z_order: ZIndex(value: 1)
)
expect(1).to_equal(1)
```

</details>

### DrawLine

#### constructs with endpoints, width, color, and z_order

1. color: EngineColor blue
2. z order: ZIndex
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = RenderCommand.DrawLine(
    x1: 0.0,
    y1: 0.0,
    x2: 100.0,
    y2: 100.0,
    width: 2.0,
    color: EngineColor.blue(),
    z_order: ZIndex(value: 3)
)
expect(1).to_equal(1)
```

</details>

### DrawSprite

#### constructs with texture_id, src/dst rects, tint, and z_order

1. tint: EngineColor white
2. z order: ZIndex
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tex = TextureId(raw: RawHandle.new(0, 1))
val src = Rect2.new(0.0, 0.0, 32.0, 32.0)
val dst = Rect2.new(100.0, 100.0, 64.0, 64.0)
val cmd = RenderCommand.DrawSprite(
    texture_id: tex,
    src_rect: src,
    dst_rect: dst,
    tint: EngineColor.white(),
    z_order: ZIndex(value: 10)
)
expect(1).to_equal(1)
```

</details>

### DrawTriangles

#### constructs with vertices, indices, color, and z_order

1. color: EngineColor yellow
2. z order: ZIndex
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v0 = Vertex2D(x: 0.0, y: 0.0, u: 0.0, v: 0.0, r: 1.0, g: 1.0, b: 1.0, a: 1.0)
val v1 = Vertex2D(x: 10.0, y: 0.0, u: 1.0, v: 0.0, r: 1.0, g: 1.0, b: 1.0, a: 1.0)
val v2 = Vertex2D(x: 5.0, y: 10.0, u: 0.5, v: 1.0, r: 1.0, g: 1.0, b: 1.0, a: 1.0)
val verts: [Vertex2D] = [v0, v1, v2]
val idxs: [i64] = [0, 1, 2]
val cmd = RenderCommand.DrawTriangles(
    vertices: verts,
    indices: idxs,
    color: EngineColor.yellow(),
    z_order: ZIndex(value: 2)
)
expect(1).to_equal(1)
```

</details>

### RenderCommandBuffer

#### starts empty after create

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = RenderCommandBuffer.create()
expect(buf.len()).to_equal(0)
```

</details>

#### increases length after push

1. var buf = RenderCommandBuffer create
2. buf push
   - Expected: buf.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf = RenderCommandBuffer.create()
buf.push(RenderCommand.Clear(color: EngineColor.black()))
expect(buf.len()).to_equal(1)
```

</details>

#### tracks multiple pushes

1. var buf = RenderCommandBuffer create
2. buf push
3. rect: Rect2 new
4. color: EngineColor red
5. z order: ZIndex
6. color: EngineColor blue
7. z order: ZIndex
   - Expected: buf.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf = RenderCommandBuffer.create()
buf.push(RenderCommand.Clear(color: EngineColor.black()))
buf.push(RenderCommand.DrawRect(
    rect: Rect2.new(0.0, 0.0, 10.0, 10.0),
    color: EngineColor.red(),
    z_order: ZIndex(value: 0)
))
buf.push(RenderCommand.DrawCircle(
    cx: 5.0, cy: 5.0, radius: 3.0,
    color: EngineColor.blue(),
    z_order: ZIndex(value: 1)
))
expect(buf.len()).to_equal(3)
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
buf.push(RenderCommand.Clear(color: EngineColor.white()))
buf.push(RenderCommand.Clear(color: EngineColor.red()))
buf.clear()
expect(buf.len()).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
