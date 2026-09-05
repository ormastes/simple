# Dxvk Vkd3d Dispatch Specification

> <details>

<!-- sdn-diagram:id=dxvk_vkd3d_dispatch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dxvk_vkd3d_dispatch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dxvk_vkd3d_dispatch_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dxvk_vkd3d_dispatch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dxvk Vkd3d Dispatch Specification

## Scenarios

### D3D9 ICD dispatch chain

#### create device has ICD instance handle > 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = dxvk_d3d9_create_device()
expect(result.is_ok).to_equal(true)
expect(result.icd_instance).to_be_greater_than(0)
```

</details>

#### create texture returns valid handle

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

#### create vertex buffer returns valid handle

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = dxvk_d3d9_create_device()
val buf = dxvk_d3d9_create_vertex_buffer(dev.device_handle, 4096)
expect(buf).to_be_greater_than(0)
```

</details>

#### draw primitive succeeds with valid device

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

#### present succeeds

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = dxvk_d3d9_create_device()
expect(dxvk_d3d9_present(dev.device_handle)).to_equal(true)
```

</details>

#### destroy releases ICD

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = dxvk_d3d9_create_device()
expect(dxvk_d3d9_destroy_device(dev.device_handle)).to_equal(true)
expect(dxvk_d3d9_present(dev.device_handle)).to_equal(false)
```

</details>

### D3D11 ICD dispatch chain

#### create device has ICD handles

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = dxvk_d3d11_create_device()
expect(result.is_ok).to_equal(true)
expect(result.icd_instance).to_be_greater_than(0)
expect(result.icd_device).to_be_greater_than(0)
```

</details>

#### swapchain present chain works

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = dxvk_d3d11_create_device()
val sc = dxvk_d3d11_create_swapchain(dev.device_handle, 1920, 1080)
expect(sc.is_ok).to_equal(true)
expect(dxvk_d3d11_present(sc.swapchain_handle)).to_equal(true)
```

</details>

#### draw succeeds

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = dxvk_d3d11_create_device()
expect(dxvk_d3d11_draw(dev.device_handle, 6)).to_equal(true)
```

</details>

#### readback target preserves handle and checksum

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = dxvk_d3d11_create_device()
val rb = dxvk_d3d11_create_readback_target(dev.device_handle, 2, 1)
expect(rb).to_be_greater_than(0)
val pixels: [u32] = [0xFF112233, 0xFF445566]
expect(dxvk_d3d11_upload_framebuffer(rb, pixels, 2, 1)).to_equal(true)
val readback = dxvk_d3d11_readback_pixels(rb)
expect(readback.is_ok).to_equal(true)
expect(readback.readback_handle).to_equal(rb)
expect(readback.pixel_count).to_equal(2)
expect(readback.checksum).to_be_greater_than(0)
```

</details>

### D3D12 ICD dispatch chain

#### create device has ICD handles

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = vkd3d_d3d12_create_device()
expect(result.is_ok).to_equal(true)
expect(result.icd_instance).to_be_greater_than(0)
expect(result.icd_device).to_be_greater_than(0)
```

</details>

#### command list execute chain works

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = vkd3d_d3d12_create_device()
val cl = vkd3d_d3d12_create_command_list(dev.device_handle)
expect(cl.is_ok).to_equal(true)
expect(vkd3d_d3d12_execute_command_lists(dev.device_handle, cl.list_handle)).to_equal(true)
```

</details>

#### fence creation with ICD reference

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = vkd3d_d3d12_create_device()
val fence = vkd3d_d3d12_create_fence(dev.device_handle)
expect(fence.is_ok).to_equal(true)
expect(fence.fence_handle).to_be_greater_than(0)
expect(fence.fence_value).to_equal(0)
```

</details>

#### root signature returns valid handle

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = vkd3d_d3d12_create_device()
val rs = vkd3d_d3d12_create_root_signature(dev.device_handle)
expect(rs).to_be_greater_than(0)
```

</details>

#### descriptor heap returns valid handle

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = vkd3d_d3d12_create_device()
val heap = vkd3d_d3d12_create_descriptor_heap(dev.device_handle, 64)
expect(heap).to_be_greater_than(0)
```

</details>

### Invalid device handle errors

#### D3D9 draw fails on invalid handle

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = dxvk_d3d9_draw_primitive(0, 3)
expect(result.is_ok).to_equal(false)
```

</details>

#### D3D11 draw fails on invalid handle

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(dxvk_d3d11_draw(0, 6)).to_equal(false)
```

</details>

#### D3D12 command list fails on invalid handle

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cl = vkd3d_d3d12_create_command_list(0)
expect(cl.is_ok).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/gpu/dxvk_vkd3d_dispatch_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- D3D9 ICD dispatch chain
- D3D11 ICD dispatch chain
- D3D12 ICD dispatch chain
- Invalid device handle errors

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
