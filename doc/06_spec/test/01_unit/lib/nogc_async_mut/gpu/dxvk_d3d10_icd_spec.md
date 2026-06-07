# Dxvk D3d10 Icd Specification

> <details>

<!-- sdn-diagram:id=dxvk_d3d10_icd_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dxvk_d3d10_icd_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dxvk_d3d10_icd_spec -> nogc_async_mut
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dxvk_d3d10_icd_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dxvk D3d10 Icd Specification

## Scenarios

### DXVK D3D10 ICD dispatch chain

#### creates a D3D10 device routed through vulkan_icd_sffi

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = dxvk_d3d10_create_device()
expect(dev.is_ok).to_equal(true)
expect(dev.device_handle).to_be_greater_than(0)
expect(dev.icd_instance).to_be_greater_than(0)
expect(dev.icd_device).to_be_greater_than(0)
expect(dev.icd_dispatch).to_be_greater_than(0)
```

</details>

#### draws vertices through ICD queue submit

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = dxvk_d3d10_create_device()
expect(dxvk_d3d10_draw(dev.device_handle, 3)).to_equal(true)
```

</details>

#### rejects draw on invalid device

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(dxvk_d3d10_draw(0, 3)).to_equal(false)
expect(dxvk_d3d10_draw(-1, 3)).to_equal(false)
```

</details>

#### rejects draw with zero vertices

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = dxvk_d3d10_create_device()
expect(dxvk_d3d10_draw(dev.device_handle, 0)).to_equal(false)
```

</details>

#### creates a render target on a valid device

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

#### rejects render target on invalid device

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(dxvk_d3d10_create_render_target(0, 1920, 1080)).to_equal(0)
```

</details>

#### rejects render target with invalid dimensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = dxvk_d3d10_create_device()
expect(dxvk_d3d10_create_render_target(dev.device_handle, 0, 1080)).to_equal(0)
expect(dxvk_d3d10_create_render_target(dev.device_handle, 1920, 0)).to_equal(0)
```

</details>

#### presents through ICD queue present

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = dxvk_d3d10_create_device()
expect(dxvk_d3d10_present(dev.device_handle)).to_equal(true)
```

</details>

#### rejects present on invalid device

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(dxvk_d3d10_present(0)).to_equal(false)
```

</details>

#### destroys a device and invalidates further use

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = dxvk_d3d10_create_device()
expect(dxvk_d3d10_destroy_device(dev.device_handle)).to_equal(true)
expect(dxvk_d3d10_draw(dev.device_handle, 3)).to_equal(false)
expect(dxvk_d3d10_present(dev.device_handle)).to_equal(false)
expect(dxvk_d3d10_destroy_device(dev.device_handle)).to_equal(false)
```

</details>

#### rejects destroy on invalid device

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(dxvk_d3d10_destroy_device(0)).to_equal(false)
expect(dxvk_d3d10_destroy_device(-1)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/gpu/dxvk_d3d10_icd_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DXVK D3D10 ICD dispatch chain

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
