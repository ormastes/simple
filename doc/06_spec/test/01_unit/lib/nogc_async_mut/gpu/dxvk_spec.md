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
| 15 | 15 | 0 | 0 |

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
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
