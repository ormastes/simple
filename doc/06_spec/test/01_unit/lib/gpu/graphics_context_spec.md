# Graphics Context Specification

> <details>

<!-- sdn-diagram:id=graphics_context_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=graphics_context_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

graphics_context_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=graphics_context_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Graphics Context Specification

## Scenarios

### GpuFormat

#### reports bytes per pixel

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rgba = GpuFormat.RGBA8
expect(rgba.bytes_per_pixel()).to_equal(4)
val r8 = GpuFormat.R8
expect(r8.bytes_per_pixel()).to_equal(1)
val rgb = GpuFormat.RGB8
expect(rgb.bytes_per_pixel()).to_equal(3)
```

</details>

#### identifies depth formats

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d32 = GpuFormat.Depth32F
expect(d32.is_depth()).to_equal(true)
val rgba = GpuFormat.RGBA8
expect(rgba.is_depth()).to_equal(false)
```

</details>

#### converts to text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(GpuFormat.BGRA8.to_text()).to_equal("BGRA8")
expect(GpuFormat.Depth24Stencil8.to_text()).to_equal("Depth24Stencil8")
```

</details>

### GpuTexture

#### creates with descriptor fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tex = GpuTexture(handle: 1, width: 256, height: 256, format: GpuFormat.RGBA8)
expect(tex.is_valid()).to_equal(true)
expect(tex.size_bytes()).to_equal(262144)
```

</details>

#### invalid when handle is zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tex = GpuTexture(handle: 0, width: 0, height: 0, format: GpuFormat.RGBA8)
expect(tex.is_valid()).to_equal(false)
```

</details>

### GpuRenderPass

#### validates handle

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rp = GpuRenderPass(handle: 42)
expect(rp.is_valid()).to_equal(true)
val bad = GpuRenderPass(handle: 0)
expect(bad.is_valid()).to_equal(false)
```

</details>

### GpuBlendMode

#### converts to text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(GpuBlendMode.AlphaBlend.to_text()).to_equal("AlphaBlend")
expect(GpuBlendMode.Additive.to_text()).to_equal("Additive")
```

</details>

### GpuTopology

#### converts to text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(GpuTopology.TriangleList.to_text()).to_equal("TriangleList")
expect(GpuTopology.LineStrip.to_text()).to_equal("LineStrip")
```

</details>

### GpuVertexFormat

#### reports size in bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(GpuVertexFormat.Float2.size_bytes()).to_equal(8)
expect(GpuVertexFormat.Float3.size_bytes()).to_equal(12)
expect(GpuVertexFormat.Float4.size_bytes()).to_equal(16)
expect(GpuVertexFormat.UByte4.size_bytes()).to_equal(4)
```

</details>

### GpuShader

#### validates handle

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vs = GpuShader(handle: 1, stage: GpuShaderStage.Vertex)
expect(vs.is_valid()).to_equal(true)
expect(vs.stage.to_text()).to_equal("Vertex")
```

</details>

### GpuGraphicsPipeline

#### validates handle

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pipe = GpuGraphicsPipeline(handle: 5)
expect(pipe.is_valid()).to_equal(true)
```

</details>

### GpuSwapchain

#### validates and stores dimensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sc = GpuSwapchain(handle: 1, width: 1920, height: 1080, format: GpuFormat.BGRA8)
expect(sc.is_valid()).to_equal(true)
expect(sc.width).to_equal(1920)
```

</details>

### GpuFramebuffer

#### reports pixel count

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fb = GpuFramebuffer(handle: 1, width: 800, height: 600)
expect(fb.size_pixels()).to_equal(480000)
```

</details>

### preferred_graphics_backend

#### returns a valid backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = preferred_graphics_backend()
# Should return Vulkan as default
expect(backend.to_text()).to_equal("Vulkan")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/graphics_context_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- GpuFormat
- GpuTexture
- GpuRenderPass
- GpuBlendMode
- GpuTopology
- GpuVertexFormat
- GpuShader
- GpuGraphicsPipeline
- GpuSwapchain
- GpuFramebuffer
- preferred_graphics_backend

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
