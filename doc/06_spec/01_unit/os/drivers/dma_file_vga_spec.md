# Dma File Vga Specification

> <details>

<!-- sdn-diagram:id=dma_file_vga_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dma_file_vga_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dma_file_vga_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dma_file_vga_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dma File Vga Specification

## Scenarios

### DMA Descriptor

#### canonical descriptor holds all required fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = DmaBuf.create(0x1000, 0x2000, 0x3000, 4096, "coherent", 1, 5)
expect(buf.vaddr).to_equal(0x1000)
expect(buf.paddr).to_equal(0x2000)
expect(buf.byte_len).to_equal(4096)
expect(buf.owner_task).to_equal(1)
expect(buf.owner_dev).to_equal(5)
```

</details>

#### release succeeds for valid owner

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = DmaBuf.create(0x1000, 0x2000, 0x3000, 4096, "coherent", 7, 2)
val msg = buf.validate_release(7)
expect(msg).to_equal("")
```

</details>

#### release rejected for wrong owner

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = DmaBuf.create(0x1000, 0x2000, 0x3000, 4096, "coherent", 7, 2)
val msg = buf.validate_release(99)
expect(msg == "").to_equal(false)
```

</details>

#### coherent sync cpu_to_dev is noop

1. var buf = DmaBuf create
2. var syncer = SyncHelper for cache
   - Expected: syncer.cpu_to_dev(buf) equals `noop`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf = DmaBuf.create(0x1000, 0x2000, 0x3000, 512, "coherent", 1, 1)
var syncer = SyncHelper.for_cache("coherent")
expect(syncer.cpu_to_dev(buf)).to_equal("noop")
```

</details>

#### flush_required sync increments flush count

1. var buf = DmaBuf create
2. var syncer = SyncHelper for cache
3. syncer cpu to dev
4. syncer dev to cpu
   - Expected: syncer.total_flushes() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf = DmaBuf.create(0x1000, 0x2000, 0x3000, 512, "flush_required", 1, 1)
var syncer = SyncHelper.for_cache("flush_required")
syncer.cpu_to_dev(buf)
syncer.dev_to_cpu(buf)
expect(syncer.total_flushes()).to_equal(2)
```

</details>

### SR-IOV Isolation

#### isolated domain with IOMMU allows VF assignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dom = IsolDomain.isolated()
expect(dom.can_assign_vf()).to_equal(true)
```

</details>

#### no-isolation domain rejects VF assignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dom = IsolDomain.none_isol()
expect(dom.can_assign_vf()).to_equal(false)
```

</details>

#### trusted mode does not advertise isolation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dom = IsolDomain.trusted()
expect(dom.advertises_isolation()).to_equal(false)
```

</details>

#### isolated domain advertises isolation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dom = IsolDomain.isolated()
expect(dom.advertises_isolation()).to_equal(true)
```

</details>

### Direct I/O

#### direct IO capability requires DMA buffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cap = DioCapability.available(4096, 1048576)
expect(cap.requires_dma_buf()).to_equal(true)
```

</details>

#### unavailable capability does not require DMA buffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cap = DioCapability.unavailable()
expect(cap.requires_dma_buf()).to_equal(false)
```

</details>

#### aligned offset passes validation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cap = DioCapability.available(4096, 1048576)
expect(cap.validate_offset(4096)).to_equal(true)
```

</details>

#### unaligned offset fails validation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cap = DioCapability.available(4096, 1048576)
expect(cap.validate_offset(100)).to_equal(false)
```

</details>

#### NVMe backend is identified correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = BlockBackend.nvme(0, 5000)
expect(backend.is_nvme()).to_equal(true)
expect(backend.is_virtio()).to_equal(false)
```

</details>

#### VirtIO-BLK backend is identified correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = BlockBackend.virtio_blk(1, 3000)
expect(backend.is_virtio()).to_equal(true)
expect(backend.is_nvme()).to_equal(false)
```

</details>

### Display Capability

#### framebuffer-mmio is not DMA capable

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cap = DisplayCap.framebuffer_mmio()
expect(cap.is_dma).to_equal(false)
expect(cap.label()).to_equal("framebuffer-mmio")
```

</details>

#### bga-write-combining is not DMA accelerated

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cap = DisplayCap.bga_write_combining()
expect(cap.is_legacy()).to_equal(true)
expect(cap.is_dma).to_equal(false)
```

</details>

#### virtio-gpu-dma is DMA capable

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cap = DisplayCap.virtio_gpu_dma()
expect(cap.is_dma).to_equal(true)
expect(cap.is_accel).to_equal(true)
```

</details>

#### dirty rect flush marks bounded region

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rect = DirtyRectFlush.region(10, 10, 100, 50)
expect(rect.is_bounded()).to_equal(true)
expect(rect.area()).to_equal(5000)
```

</details>

#### wrong-owner DMA free is denied

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gate = DmaOwnerGate.check(1, 2)
expect(gate.is_allowed()).to_equal(false)
expect(gate.denial_reason() == "").to_equal(false)
```

</details>

#### display falls back to framebuffer when DMA unavailable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dp = DisplayFallback.fallback_only()
expect(dp.effective_path()).to_equal("framebuffer-mmio")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/drivers/dma_file_vga_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DMA Descriptor
- SR-IOV Isolation
- Direct I/O
- Display Capability

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
