# Vulkan Backend Specification

> 1. var backend = vk backend new

<!-- sdn-diagram:id=vulkan_backend_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vulkan_backend_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vulkan_backend_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vulkan_backend_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vulkan Backend Specification

## Scenarios

### VulkanBackend

#### empty picture produces empty CommandBufferRecord

1. var backend = vk backend new
   - Expected: cb.commands.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = vk_backend_new()
val picture = sk_picture_empty()
val cull = SkRect(left: 0.0, top: 0.0, right: 100.0, bottom: 100.0)
val cb = backend.render_picture(picture, cull)
expect(cb.commands.len()).to_equal(0)
```

</details>

#### pipeline cache: same paint twice yields 1 unique pipeline and 2 cache hits

1. var backend = vk backend new
   - Expected: p1.pipeline_id equals `p2.pipeline_id`
   - Expected: backend.pipeline_cache.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = vk_backend_new()
val paint = _fill_paint()
# Prime cache with first op
val p1 = backend.get_or_compile_pipeline(paint)
# Second call — should hit cache
val p2 = backend.get_or_compile_pipeline(paint)
expect(p1.pipeline_id).to_equal(p2.pipeline_id)
expect(backend.pipeline_cache.len()).to_equal(1)
```

</details>

#### different blend modes produce different PipelineKeys

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val paint_src_over = _blend_paint(SkBlendMode.SrcOver)
val paint_multiply = _blend_paint(SkBlendMode.Multiply)
val key1 = PipelineKey(blend_mode: paint_src_over.blend_mode, style: paint_src_over.style, shader_kind: ShaderKind.SolidColor)
val key2 = PipelineKey(blend_mode: paint_multiply.blend_mode, style: paint_multiply.style, shader_kind: ShaderKind.SolidColor)
val same = key1.equals(key2)
expect(same).to_equal(false)
```

</details>

#### different SkPaintStyle (fill vs stroke) produce different PipelineKeys

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val paint_fill   = _fill_paint()
val paint_stroke = _stroke_paint()
val key1 = PipelineKey(blend_mode: paint_fill.blend_mode,   style: paint_fill.style,   shader_kind: ShaderKind.SolidColor)
val key2 = PipelineKey(blend_mode: paint_stroke.blend_mode, style: paint_stroke.style, shader_kind: ShaderKind.SolidColor)
val same = key1.equals(key2)
expect(same).to_equal(false)
```

</details>

#### triangulate_path of a triangle yields 3 vertices (1 triangle)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = _triangle_path()
val verts = triangulate_path(path)
expect(verts.len()).to_equal(3)
```

</details>

#### triangulate_path of a square yields 6 vertices (2 triangles)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = _square_path()
val verts = triangulate_path(path)
expect(verts.len()).to_equal(6)
```

</details>

#### build_vertex_buffer computes correct byte_count (verts * 16 bytes)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = _triangle_path()
val verts = triangulate_path(path)
val vbuf = build_vertex_buffer(verts)
val expected = verts.len() * 16
expect(vbuf.byte_count).to_equal(expected)
```

</details>

#### render_pass_for_save_layer returns RenderPassDesc with matching bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bounds = SkRect(left: 10.0, top: 20.0, right: 80.0, bottom: 60.0)
val rp = render_pass_for_save_layer(bounds)
val left_ok  = rp.bounds.left  == 10.0
val top_ok   = rp.bounds.top   == 20.0
val right_ok = rp.bounds.right == 80.0
val bot_ok   = rp.bounds.bottom == 60.0
expect(left_ok).to_equal(true)
expect(top_ok).to_equal(true)
expect(right_ok).to_equal(true)
expect(bot_ok).to_equal(true)
```

</details>

#### render_picture reuses pipeline cache across repeated ops

1. var backend = vk backend new
   - Expected: cb.commands.len() equals `4`
   - Expected: cb.unique_pipelines equals `1`
   - Expected: cb.pipeline_cache_hits equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = vk_backend_new()
val cull = SkRect(left: 0.0, top: 0.0, right: 100.0, bottom: 100.0)
val cb = backend.render_picture(_picture_with_ops(2), cull)
expect(cb.commands.len()).to_equal(4)
expect(cb.unique_pipelines).to_equal(1)
expect(cb.pipeline_cache_hits).to_equal(1)
```

</details>

#### submit accepts bound draw commands and reports deterministic accounting

1. var backend = vk backend new
   - Expected: submission.ok is true
   - Expected: submission.submitted_commands equals `4`
   - Expected: submission.draw_commands equals `2`
   - Expected: submission.rejected_commands equals `0`
   - Expected: submission.last_pipeline_id equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = vk_backend_new()
val cull = SkRect(left: 0.0, top: 0.0, right: 100.0, bottom: 100.0)
val cb = backend.render_picture(_picture_with_ops(2), cull)
val submission = backend.submit(cb)
expect(submission.ok).to_equal(true)
expect(submission.submitted_commands).to_equal(4)
expect(submission.draw_commands).to_equal(2)
expect(submission.rejected_commands).to_equal(0)
expect(submission.last_pipeline_id).to_equal(1)
```

</details>

#### submit rejects draw commands without a matching bound pipeline

1. var backend = vk backend new
   - Expected: submission.ok is false
   - Expected: submission.submitted_commands equals `0`
   - Expected: submission.draw_commands equals `0`
   - Expected: submission.rejected_commands equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = vk_backend_new()
val cull = SkRect(left: 0.0, top: 0.0, right: 100.0, bottom: 100.0)
val draw = VkCommand(
    kind: VkCommandKind.Draw,
    pipeline_id: 7,
    vertex_count: 3,
    descriptor_set_id: 0,
    render_pass_bounds: cull
)
val commands = [draw]
val cb = CommandBufferRecord(commands: commands, pipeline_cache_hits: 0, unique_pipelines: 0)
val submission = backend.submit(cb)
expect(submission.ok).to_equal(false)
expect(submission.submitted_commands).to_equal(0)
expect(submission.draw_commands).to_equal(0)
expect(submission.rejected_commands).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/skia/vulkan_backend_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- VulkanBackend

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
