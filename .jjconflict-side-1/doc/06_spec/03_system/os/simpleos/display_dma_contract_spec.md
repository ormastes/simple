# Display Dma Contract Specification

> <details>

<!-- sdn-diagram:id=display_dma_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=display_dma_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

display_dma_contract_spec -> std
display_dma_contract_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=display_dma_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Display Dma Contract Specification

## Scenarios

### SimpleOS display DMA and damage contracts

#### canonical DMA descriptors

#### keeps CPU, host physical, and device addresses explicit

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val desc = DeviceDmaDescriptor(
    virt_addr: 0x1000,
    phys_addr: 0x2000,
    device_addr: 0x3000,
    size_bytes: 4096,
    cache_policy: DMA_CACHE_FLUSH_REQUIRED,
    owner_task: 7,
    owner_device: 0x1050,
    allocation_id: 44
)
expect(desc.is_valid()).to_equal(true)
expect(desc.cpu_addr()).to_equal(0x1000)
expect(desc.host_phys_addr()).to_equal(0x2000)
expect(desc.dma_addr()).to_equal(0x3000)
expect(desc.len()).to_equal(4096)
```

</details>

#### converts legacy SharedDmaBuffer to the canonical shape

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = SharedDmaBuffer(
    virt_addr: 0x4000,
    phys_addr: 0x5000,
    device_addr: 0x6000,
    size_bytes: 8192,
    cache_policy: DMA_CACHE_WRITE_COMBINING,
    owner_task: 7,
    owner_device: 0x1050,
    allocation_id: 45
)
val desc = buf.into_descriptor()
expect(desc.cpu_addr()).to_equal(0x4000)
expect(desc.host_phys_addr()).to_equal(0x5000)
expect(desc.dma_addr()).to_equal(0x6000)
expect(desc.len()).to_equal(8192)
```

</details>

#### framebuffer dirty rectangles

#### records bounded damage for rectangle drawing

1. var fb = FramebufferDriver from buffer
2. fb fill rect
   - Expected: dirty.valid is true
   - Expected: dirty.x1 equals `4`
   - Expected: dirty.y1 equals `3`
   - Expected: dirty.x2 equals `12`
   - Expected: dirty.y2 equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fb = FramebufferDriver.from_buffer(32, 16)
fb.fill_rect(4, 3, 8, 5, Color.red())
val dirty = fb.dirty_rect()
expect(dirty.valid).to_equal(true)
expect(dirty.x1).to_equal(4)
expect(dirty.y1).to_equal(3)
expect(dirty.x2).to_equal(12)
expect(dirty.y2).to_equal(8)
```

</details>

#### merges and clamps damage to framebuffer bounds

1. var fb = FramebufferDriver from buffer
2. fb fill rect
3. fb put pixel
   - Expected: dirty.x1 equals `2`
   - Expected: dirty.y1 equals `1`
   - Expected: dirty.x2 equals `32`
   - Expected: dirty.y2 equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fb = FramebufferDriver.from_buffer(32, 16)
fb.fill_rect(30, 14, 8, 8, Color.green())
fb.put_pixel(2, 1, Color.blue())
val dirty = fb.dirty_rect()
expect(dirty.x1).to_equal(2)
expect(dirty.y1).to_equal(1)
expect(dirty.x2).to_equal(32)
expect(dirty.y2).to_equal(16)
```

</details>

#### clears damage on present

1. var fb = FramebufferDriver from buffer
2. fb put pixel
   - Expected: fb.dirty_rect().valid is true
3. fb swap buffers
   - Expected: fb.dirty_rect().valid is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fb = FramebufferDriver.from_buffer(32, 16)
fb.put_pixel(1, 1, Color.white())
expect(fb.dirty_rect().valid).to_equal(true)
fb.swap_buffers()
expect(fb.dirty_rect().valid).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/simpleos/display_dma_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS display DMA and damage contracts

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
