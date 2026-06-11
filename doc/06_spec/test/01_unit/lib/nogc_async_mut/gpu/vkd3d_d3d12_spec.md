# Vkd3d D3d12 Specification

> <details>

<!-- sdn-diagram:id=vkd3d_d3d12_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vkd3d_d3d12_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vkd3d_d3d12_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vkd3d_d3d12_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vkd3d D3d12 Specification

## Scenarios

### VKD3D-Proton D3D12 translation

#### create_device returns is_ok=true with positive handle

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = vkd3d_d3d12_create_device()
expect(result.is_ok).to_equal(true)
expect(result.device_handle).to_be_greater_than(0)
```

</details>

#### create_command_list returns is_ok=true on valid device

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = vkd3d_d3d12_create_device()
val cl = vkd3d_d3d12_create_command_list(dev.device_handle)
expect(cl.is_ok).to_equal(true)
expect(cl.list_handle).to_be_greater_than(0)
```

</details>

#### create_command_list returns error on invalid device

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cl = vkd3d_d3d12_create_command_list(0)
expect(cl.is_ok).to_equal(false)
```

</details>

#### execute_command_lists returns true on valid handles

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = vkd3d_d3d12_create_device()
val cl = vkd3d_d3d12_create_command_list(dev.device_handle)
expect(vkd3d_d3d12_execute_command_lists(dev.device_handle, cl.list_handle)).to_equal(true)
```

</details>

#### execute_command_lists returns false on invalid device

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(vkd3d_d3d12_execute_command_lists(0, 1)).to_equal(false)
```

</details>

#### create_fence returns is_ok=true with fence_value=0

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

#### create_fence returns error on invalid device

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fence = vkd3d_d3d12_create_fence(0)
expect(fence.is_ok).to_equal(false)
```

</details>

#### create_root_signature returns positive handle

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

#### create_root_signature returns 0 on invalid device

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(vkd3d_d3d12_create_root_signature(0)).to_equal(0)
```

</details>

#### create_descriptor_heap returns positive handle

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

#### create_descriptor_heap returns 0 on invalid inputs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(vkd3d_d3d12_create_descriptor_heap(0, 64)).to_equal(0)
val dev = vkd3d_d3d12_create_device()
expect(vkd3d_d3d12_create_descriptor_heap(dev.device_handle, 0)).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/gpu/vkd3d_d3d12_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- VKD3D-Proton D3D12 translation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
