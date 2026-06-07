# Vulkan Icd Virtio Specification

> 1. venus icd disconnect

<!-- sdn-diagram:id=vulkan_icd_virtio_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vulkan_icd_virtio_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vulkan_icd_virtio_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vulkan_icd_virtio_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vulkan Icd Virtio Specification

## Scenarios

### Virtio Venus ICD transport

#### connect with valid device path succeeds

1. venus icd disconnect


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = venus_icd_connect("/dev/vgpu0", 256)
expect(ok).to_equal(true)
venus_icd_disconnect()
```

</details>

#### connect with empty path fails

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = venus_icd_connect("", 256)
expect(ok).to_equal(false)
```

</details>

#### is_connected reflects state

1. venus icd connect
   - Expected: venus_icd_is_connected() is true
2. venus icd disconnect
   - Expected: venus_icd_is_connected() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
venus_icd_connect("/dev/vgpu0", 256)
expect(venus_icd_is_connected()).to_equal(true)
venus_icd_disconnect()
expect(venus_icd_is_connected()).to_equal(false)
```

</details>

#### create_instance returns valid handle

1. venus icd connect
   - Expected: result.is_ok is true
2. venus icd disconnect


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
venus_icd_connect("/dev/vgpu0", 256)
val result = venus_icd_create_instance()
expect(result.is_ok).to_equal(true)
expect(result.handle).to_be_greater_than(0)
venus_icd_disconnect()
```

</details>

#### create_device with valid instance succeeds

1. venus icd connect
   - Expected: dev.is_ok is true
2. venus icd disconnect


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
venus_icd_connect("/dev/vgpu0", 256)
val inst = venus_icd_create_instance()
val dev = venus_icd_create_device(inst.handle)
expect(dev.is_ok).to_equal(true)
expect(dev.handle).to_be_greater_than(0)
venus_icd_disconnect()
```

</details>

#### create_device with invalid instance fails

1. venus icd connect
   - Expected: result.is_ok is false
   - Expected: result.error equals `invalid-instance`
2. venus icd disconnect


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
venus_icd_connect("/dev/vgpu0", 256)
val result = venus_icd_create_device(0)
expect(result.is_ok).to_equal(false)
expect(result.error).to_equal("invalid-instance")
venus_icd_disconnect()
```

</details>

#### allocate_memory returns valid handle

1. venus icd connect
   - Expected: mem.is_ok is true
2. venus icd disconnect


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
venus_icd_connect("/dev/vgpu0", 256)
val inst = venus_icd_create_instance()
val dev = venus_icd_create_device(inst.handle)
val mem = venus_icd_allocate_memory(dev.handle, 4096)
expect(mem.is_ok).to_equal(true)
expect(mem.handle).to_be_greater_than(0)
venus_icd_disconnect()
```

</details>

#### create_buffer returns valid handle

1. venus icd connect
   - Expected: buf.is_ok is true
2. venus icd disconnect


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
venus_icd_connect("/dev/vgpu0", 256)
val inst = venus_icd_create_instance()
val dev = venus_icd_create_device(inst.handle)
val buf = venus_icd_create_buffer(dev.handle, 2048)
expect(buf.is_ok).to_equal(true)
expect(buf.handle).to_be_greater_than(0)
venus_icd_disconnect()
```

</details>

#### destroy_instance accepted

1. venus icd connect
2. venus icd destroy instance
   - Expected: 1 equals `1`
3. venus icd disconnect


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
venus_icd_connect("/dev/vgpu0", 256)
val inst = venus_icd_create_instance()
venus_icd_destroy_instance(inst.handle)
expect(1).to_equal(1)
venus_icd_disconnect()
```

</details>

#### disconnect resets state

1. venus icd connect
2. venus icd disconnect
   - Expected: venus_icd_is_connected() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
venus_icd_connect("/dev/vgpu0", 256)
venus_icd_disconnect()
expect(venus_icd_is_connected()).to_equal(false)
```

</details>

#### protocol_version returns expected value

1. venus icd connect
   - Expected: venus_icd_protocol_version() equals `1`
2. venus icd disconnect


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
venus_icd_connect("/dev/vgpu0", 256)
expect(venus_icd_protocol_version()).to_equal(1)
venus_icd_disconnect()
```

</details>

#### operations fail when not connected

1. venus icd disconnect
   - Expected: result.is_ok is false
   - Expected: result.error equals `not-connected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
venus_icd_disconnect()
val result = venus_icd_create_instance()
expect(result.is_ok).to_equal(false)
expect(result.error).to_equal("not-connected")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/gpu/vulkan_icd_virtio_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Virtio Venus ICD transport

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
