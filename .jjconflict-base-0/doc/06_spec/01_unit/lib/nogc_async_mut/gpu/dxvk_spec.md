# Dxvk Specification

> <details>

<!-- sdn-diagram:id=dxvk_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dxvk_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dxvk_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dxvk_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dxvk Specification

## Scenarios

### DXVK D3D9 translation

#### create_device returns is_ok=true

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = dxvk_d3d9_create_device()
expect(result.is_ok).to_equal(true)
expect(result.device_handle).to_be_greater_than(0)
```

</details>

#### create_texture returns positive handle on valid device

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = dxvk_d3d9_create_device()
val tex = dxvk_d3d9_create_texture(dev.device_handle, 256, 256)
expect(tex).to_be_greater_than(0)
```

</details>

#### create_texture returns 0 on invalid device

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tex = dxvk_d3d9_create_texture(0, 256, 256)
expect(tex).to_equal(0)
```

</details>

#### draw_primitive returns is_ok=true with vertex count

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = dxvk_d3d9_create_device()
val result = dxvk_d3d9_draw_primitive(dev.device_handle, 3)
expect(result.is_ok).to_equal(true)
expect(result.vertex_count).to_equal(3)
```

</details>

#### draw_primitive returns error on invalid device

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = dxvk_d3d9_draw_primitive(0, 3)
expect(result.is_ok).to_equal(false)
```

</details>

### DXVK D3D10 translation

#### create_device returns is_ok=true

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = dxvk_d3d10_create_device()
expect(result.is_ok).to_equal(true)
expect(result.device_handle).to_be_greater_than(0)
```

</details>

#### draw returns true on valid device with vertices

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = dxvk_d3d10_create_device()
expect(dxvk_d3d10_draw(dev.device_handle, 6)).to_equal(true)
```

</details>

#### draw returns false on invalid device

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(dxvk_d3d10_draw(0, 6)).to_equal(false)
```

</details>

#### create_render_target returns positive handle

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = dxvk_d3d10_create_device()
val rt = dxvk_d3d10_create_render_target(dev.device_handle, 1920, 1080)
expect(rt).to_be_greater_than(0)
```

</details>

#### create_render_target returns 0 on invalid device

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rt = dxvk_d3d10_create_render_target(0, 1920, 1080)
expect(rt).to_equal(0)
```

</details>

### DXVK D3D11 translation

#### create_device returns is_ok=true

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = dxvk_d3d11_create_device()
expect(result.is_ok).to_equal(true)
expect(result.device_handle).to_be_greater_than(0)
```

</details>

#### create_swapchain returns is_ok=true on valid device

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = dxvk_d3d11_create_device()
val sc = dxvk_d3d11_create_swapchain(dev.device_handle, 1920, 1080)
expect(sc.is_ok).to_equal(true)
expect(sc.swapchain_handle).to_be_greater_than(0)
```

</details>

#### create_swapchain returns error on invalid device

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sc = dxvk_d3d11_create_swapchain(0, 800, 600)
expect(sc.is_ok).to_equal(false)
```

</details>

#### present returns true on valid swapchain

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = dxvk_d3d11_create_device()
val sc = dxvk_d3d11_create_swapchain(dev.device_handle, 800, 600)
expect(dxvk_d3d11_present(sc.swapchain_handle)).to_equal(true)
```

</details>

#### probe_device returns positive evidence and releases probe device

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = dxvk_d3d11_probe_device()
expect(probe.is_ok).to_equal(true)
expect(probe.device_handle).to_be_greater_than(0)
val readback = dxvk_d3d11_create_readback_target(probe.device_handle, 1, 1)
expect(readback).to_equal(0)
```

</details>

#### create_render_target returns positive handle

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = dxvk_d3d11_create_device()
val rt = dxvk_d3d11_create_render_target(dev.device_handle, 800, 600)
expect(rt).to_be_greater_than(0)
```

</details>

#### readback target returns uploaded pixels with checksum

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = dxvk_d3d11_create_device()
val rb = dxvk_d3d11_create_readback_target(dev.device_handle, 2, 2)
expect(rb).to_be_greater_than(0)
val pixels: [u32] = [0xFF0000FF, 0xFF00FF00, 0xFFFF0000, 0xFFFFFFFF]
expect(dxvk_d3d11_upload_framebuffer(rb, pixels, 2, 2)).to_equal(true)
val readback = dxvk_d3d11_readback_pixels(rb)
expect(readback.is_ok).to_equal(true)
expect(readback.readback_handle).to_equal(rb)
expect(readback.pixel_count).to_equal(4)
expect(readback.pixels[0]).to_equal(0xFF0000FF)
expect(readback.checksum).to_be_greater_than(0)
```

</details>

#### present_readback owns upload, validation, and checksum policy

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = dxvk_d3d11_create_device()
val sc = dxvk_d3d11_create_swapchain(dev.device_handle, 2, 2)
val rb = dxvk_d3d11_create_readback_target(dev.device_handle, 2, 2)
val pixels: [u32] = [0xFF000000, 0xFF111111, 0xFF222222, 0xFF333333]
val result = dxvk_d3d11_present_readback(sc.swapchain_handle, rb, pixels, 2, 2)
expect(result.present_ok).to_equal(true)
expect(result.upload_ok).to_equal(true)
expect(result.readback_ok).to_equal(true)
expect(result.readback_handle).to_equal(rb)
expect(result.pixel_count).to_equal(4)
expect(result.pixels[3]).to_equal(0xFF333333)
expect(result.checksum).to_be_greater_than(0)
```

</details>

#### present_readback accepts all-zero frames as valid device readback

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = dxvk_d3d11_create_device()
val sc = dxvk_d3d11_create_swapchain(dev.device_handle, 2, 2)
val rb = dxvk_d3d11_create_readback_target(dev.device_handle, 2, 2)
val pixels: [u32] = [0, 0, 0, 0]
val result = dxvk_d3d11_present_readback(sc.swapchain_handle, rb, pixels, 2, 2)
expect(result.readback_ok).to_equal(true)
expect(result.pixel_count).to_equal(4)
expect(result.checksum).to_equal(0)
```

</details>

#### destroyed readback target rejects reads

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = dxvk_d3d11_create_device()
val rb = dxvk_d3d11_create_readback_target(dev.device_handle, 1, 1)
expect(rb).to_be_greater_than(0)
expect(dxvk_d3d11_destroy_readback_target(rb)).to_equal(true)
val readback = dxvk_d3d11_readback_pixels(rb)
expect(readback.is_ok).to_equal(false)
expect(readback.error).to_equal("invalid-readback-target")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/gpu/dxvk_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DXVK D3D9 translation
- DXVK D3D10 translation
- DXVK D3D11 translation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
