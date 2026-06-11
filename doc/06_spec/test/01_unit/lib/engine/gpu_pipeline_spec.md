# Gpu Pipeline Specification

> <details>

<!-- sdn-diagram:id=gpu_pipeline_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gpu_pipeline_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gpu_pipeline_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gpu_pipeline_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gpu Pipeline Specification

## Scenarios

### GpuVertex2D

#### creates vertex from position, UV, and color

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val white = EngineColor(r: 1.0, g: 1.0, b: 1.0, a: 1.0)
val v = GpuVertex2D.from_pos_uv_color(10.0, 20.0, 0.0, 0.0, white)
expect(v.pos_x).to_equal(10.0)
expect(v.pos_y).to_equal(20.0)
expect(v.uv_x).to_equal(0.0)
expect(v.color_a).to_equal(1.0)
```

</details>

### SpriteBatch

#### starts empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val batch = SpriteBatch.create(0)
expect(batch.quad_count).to_equal(0)
expect(batch.vertices.len()).to_equal(0)
expect(batch.indices.len()).to_equal(0)
```

</details>

#### adds a quad with 4 vertices and 6 indices

1. var batch = SpriteBatch create
2. batch add quad
   - Expected: batch.quad_count equals `1`
   - Expected: batch.vertices.len() equals `4`
   - Expected: batch.indices.len() equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var batch = SpriteBatch.create(0)
val red = EngineColor(r: 1.0, g: 0.0, b: 0.0, a: 1.0)
batch.add_quad(0.0, 0.0, 100.0, 100.0, 0.0, 0.0, 1.0, 1.0, red)
expect(batch.quad_count).to_equal(1)
expect(batch.vertices.len()).to_equal(4)
expect(batch.indices.len()).to_equal(6)
```

</details>

#### adds multiple quads

1. var batch = SpriteBatch create
2. batch add quad
3. batch add quad
   - Expected: batch.quad_count equals `2`
   - Expected: batch.vertices.len() equals `8`
   - Expected: batch.indices.len() equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var batch = SpriteBatch.create(0)
val c = EngineColor(r: 0.5, g: 0.5, b: 0.5, a: 1.0)
batch.add_quad(0.0, 0.0, 10.0, 10.0, 0.0, 0.0, 1.0, 1.0, c)
batch.add_quad(20.0, 20.0, 30.0, 30.0, 0.0, 0.0, 1.0, 1.0, c)
expect(batch.quad_count).to_equal(2)
expect(batch.vertices.len()).to_equal(8)
expect(batch.indices.len()).to_equal(12)
```

</details>

### GpuRenderer2D

#### creates with dimensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val renderer = GpuRenderer2D.create(800, 600)
expect(renderer.screen_width).to_equal(800)
expect(renderer.screen_height).to_equal(600)
```

</details>

#### resizes

1. var renderer = GpuRenderer2D create
2. renderer resize
   - Expected: renderer.screen_width equals `1920`
   - Expected: renderer.screen_height equals `1080`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var renderer = GpuRenderer2D.create(800, 600)
renderer.resize(1920, 1080)
expect(renderer.screen_width).to_equal(1920)
expect(renderer.screen_height).to_equal(1080)
```

</details>

#### converts screen coords to NDC

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val renderer = GpuRenderer2D.create(800, 600)
val ndc = renderer.screen_to_ndc(400.0, 300.0)
# Center of screen should be (0, 0)
val nx_i = ndc.x * 1000.0
val ny_i = ndc.y * 1000.0
expect(nx_i).to_be_greater_than(-1.0)
expect(nx_i).to_be_less_than(1.0)
expect(ny_i).to_be_greater_than(-1.0)
expect(ny_i).to_be_less_than(1.0)
```

</details>

#### submits DrawRect commands and tracks stats

1. var renderer = GpuRenderer2D create
2. var buf = RenderCommandBuffer
3. buf commands push
   - Expected: stats.draw_calls equals `1`
   - Expected: stats.triangles equals `2`
   - Expected: stats.vertices equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var renderer = GpuRenderer2D.create(100, 100)
var buf = RenderCommandBuffer(commands: [])
val red = EngineColor(r: 1.0, g: 0.0, b: 0.0, a: 1.0)
val rect = Rect2(x: 10.0, y: 10.0, width: 50.0, height: 50.0)
buf.commands.push(RenderCommand.DrawRect(rect: rect, color: red, z_order: ZIndex(value: 0)))
val stats = renderer.submit_commands(buf)
expect(stats.draw_calls).to_equal(1)
expect(stats.triangles).to_equal(2)
expect(stats.vertices).to_equal(4)
```

</details>

#### batches sprites by texture

1. var renderer = GpuRenderer2D create
2. var buf = RenderCommandBuffer
3. buf commands push
4. buf commands push
   - Expected: stats.draw_calls equals `2`
   - Expected: stats.triangles equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var renderer = GpuRenderer2D.create(100, 100)
var buf = RenderCommandBuffer(commands: [])
val tint = EngineColor(r: 1.0, g: 1.0, b: 1.0, a: 1.0)
val tex_id = TextureId(raw: RawHandle(index: 1, generation: Generation(value: 1)))
val src = Rect2(x: 0.0, y: 0.0, width: 32.0, height: 32.0)
val dst1 = Rect2(x: 0.0, y: 0.0, width: 64.0, height: 64.0)
val dst2 = Rect2(x: 64.0, y: 0.0, width: 64.0, height: 64.0)
buf.commands.push(RenderCommand.DrawSprite(texture_id: tex_id, src_rect: src, dst_rect: dst1, tint: tint, z_order: ZIndex(value: 0)))
buf.commands.push(RenderCommand.DrawSprite(texture_id: tex_id, src_rect: src, dst_rect: dst2, tint: tint, z_order: ZIndex(value: 0)))
val stats = renderer.submit_commands(buf)
expect(stats.draw_calls).to_equal(2)
expect(stats.triangles).to_equal(4)
```

</details>

#### flushes batch on texture change

1. var renderer = GpuRenderer2D create
2. renderer begin frame
3. renderer current batch = SpriteBatch create
4. renderer current batch add quad
5. renderer  ensure batch
   - Expected: renderer.batches.len() equals `1`
   - Expected: renderer.current_batch.texture_handle equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var renderer = GpuRenderer2D.create(100, 100)
renderer.begin_frame()
val c = EngineColor(r: 1.0, g: 1.0, b: 1.0, a: 1.0)
renderer.current_batch = SpriteBatch.create(1)
renderer.current_batch.add_quad(0.0, 0.0, 10.0, 10.0, 0.0, 0.0, 1.0, 1.0, c)
# Changing texture should flush
renderer._ensure_batch(2)
expect(renderer.batches.len()).to_equal(1)
expect(renderer.current_batch.texture_handle).to_equal(2)
```

</details>

### ImageData

#### creates valid image data

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pixels: [i64] = [0, 0, 0, 0]
val img = create_image_data(2, 2, pixels)
expect(img.is_valid()).to_equal(true)
expect(img.pixel_count()).to_equal(4)
expect(img.channels).to_equal(4)
```

</details>

#### reports size in bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pixels: [i64] = [0, 0, 0, 0, 0, 0, 0, 0, 0]
val img = create_image_data(3, 3, pixels)
expect(img.size_bytes()).to_equal(36)
```

</details>

### FontHandle

#### invalid handle returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val font = FontHandle(handle: 0, path: "test.ttf")
expect(font.is_valid()).to_equal(false)
```

</details>

#### valid handle returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val font = FontHandle(handle: 1, path: "test.ttf")
expect(font.is_valid()).to_equal(true)
```

</details>

### GlyphBitmap

#### validates dimensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val metrics = GlyphMetrics(width: 8, height: 12, advance: 10, codepoint: 65)
val glyph = GlyphBitmap(width: 8, height: 12, pixels: [], metrics: metrics)
expect(glyph.is_valid()).to_equal(true)
```

</details>

#### invalid when zero size

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val metrics = GlyphMetrics(width: 0, height: 0, advance: 0, codepoint: 0)
val glyph = GlyphBitmap(width: 0, height: 0, pixels: [], metrics: metrics)
expect(glyph.is_valid()).to_equal(false)
```

</details>

### TextAlign

#### has string representation

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val left = TextAlign.Left
val center = TextAlign.Center
val right = TextAlign.Right
expect(left.to_text()).to_equal("Left")
expect(center.to_text()).to_equal("Center")
expect(right.to_text()).to_equal("Right")
```

</details>

### TextStyle

#### creates default style

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val font = FontHandle(handle: 1, path: "test.ttf")
val style = TextStyle.default_style(font)
expect(style.size_px).to_equal(16)
expect(style.color.r).to_equal(1.0)
expect(style.line_spacing).to_equal(1.2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/gpu_pipeline_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- GpuVertex2D
- SpriteBatch
- GpuRenderer2D
- ImageData
- FontHandle
- GlyphBitmap
- TextAlign
- TextStyle

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
