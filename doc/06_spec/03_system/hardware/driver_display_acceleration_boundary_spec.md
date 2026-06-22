# Driver Display Acceleration Boundary Specification

> 1. var fb = FramebufferDriver from buffer

<!-- sdn-diagram:id=driver_display_acceleration_boundary_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=driver_display_acceleration_boundary_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

driver_display_acceleration_boundary_spec -> std
driver_display_acceleration_boundary_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=driver_display_acceleration_boundary_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Driver Display Acceleration Boundary Specification

## Scenarios

### FR-DRIVER-0011 display acceleration boundary

#### framebuffer MMIO

#### tracks and flushes only dirty framebuffer rectangles

1. var fb = FramebufferDriver from buffer
2. fb fill rect
   - Expected: dirty.valid is true
   - Expected: dirty.x1 equals `8`
   - Expected: dirty.y1 equals `4`
   - Expected: dirty.x2 equals `18`
   - Expected: dirty.y2 equals `10`
3. fb flush dirty rects
   - Expected: fb.dirty_rect().valid is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fb = FramebufferDriver.from_buffer(64, 32)
fb.fill_rect(8, 4, 10, 6, Color.red())
val dirty = fb.dirty_rect()
expect(dirty.valid).to_equal(true)
expect(dirty.x1).to_equal(8)
expect(dirty.y1).to_equal(4)
expect(dirty.x2).to_equal(18)
expect(dirty.y2).to_equal(10)
fb.flush_dirty_rects()
expect(fb.dirty_rect().valid).to_equal(false)
```

</details>

#### reports framebuffer-mmio as write-combining and non-executable

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val summary = framebuffer_mmio_summary(1024u32, 768u32)
expect(summary.backend_kind).to_equal("framebuffer-mmio")
expect(summary.flush_mode).to_equal("dirty-rect")
expect(summary.cache_policy).to_equal("write-combining")
expect(summary.dma_accelerated).to_equal(false)
expect(summary.executable_mapping).to_equal(false)
```

</details>

#### VirtIO-GPU DMA

#### reports virtio-gpu-dma as the only DMA accelerated display backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val summary = virtio_gpu_dma_summary(true)
expect(summary.backend_kind).to_equal("virtio-gpu-dma")
expect(summary.dma_accelerated).to_equal(true)
expect(summary.executable_mapping).to_equal(false)
```

</details>

#### validates canonical shared DMA transfer buffers

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(virtio_gpu_transfer_buffer_valid(dma(DmaCachePolicy.Coherent, 0x4000u64))).to_equal(true)
expect(virtio_gpu_transfer_buffer_valid(dma(DmaCachePolicy.FlushRequired, 0x8000u64))).to_equal(true)
expect(virtio_gpu_transfer_buffer_valid(dma(DmaCachePolicy.WriteCombining, 0x8000u64))).to_equal(false)
expect(virtio_gpu_transfer_buffer_valid(dma(DmaCachePolicy.Coherent, 0x4100u64))).to_equal(false)
```

</details>

#### backend selection

#### selects virtio-gpu-dma over framebuffer-mmio when GPU is present

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(display_select_summary(true).backend_kind).to_equal("virtio-gpu-dma")
expect(display_select_summary(false).backend_kind).to_equal("framebuffer-mmio")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/hardware/driver_display_acceleration_boundary_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- FR-DRIVER-0011 display acceleration boundary

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
