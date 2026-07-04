# Nvme Queue Resources Specification

> <details>

<!-- sdn-diagram:id=nvme_queue_resources_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=nvme_queue_resources_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

nvme_queue_resources_spec -> std
nvme_queue_resources_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=nvme_queue_resources_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nvme Queue Resources Specification

## Scenarios

### NVMe queue resources

#### derives doorbell stride bytes from controller DSTRD

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(nvme_dstrd_to_doorbell_stride_bytes(0u32)).to_equal(4u32)
expect(nvme_dstrd_to_doorbell_stride_bytes(1u32)).to_equal(8u32)
expect(nvme_dstrd_to_doorbell_stride_bytes(7u32)).to_equal(512u32)
expect(nvme_dstrd_to_doorbell_stride_bytes(8u32)).to_equal(0u32)
```

</details>

#### builds a reusable queue pair from freestanding-owned MMIO and DMA resources

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = _resources()
val q = nvme_queue_pair_from_resources(r).unwrap()

expect(q.qid).to_equal(1u16)
expect(q.depth).to_equal(64u16)
expect(q.sq_phys).to_equal(0x200000u64)
expect(q.cq_phys).to_equal(0x210000u64)
expect(q.sq_tail).to_equal(0u16)
expect(q.cq_head).to_equal(0u16)
expect(q.phase).to_equal(1u8)
expect(q.sq_doorbell).to_equal(nvme_sq_doorbell_addr(r.bar0_virt, 1u16, 4u32))
expect(q.cq_doorbell).to_equal(nvme_cq_doorbell_addr(r.bar0_virt, 1u16, 4u32))
```

</details>

#### rejects missing or unsafe resources before queue submission can start

1. var r =  resources
   - Expected: nvme_queue_resources_reason(r) equals `nvme-queue-depth-zero`
2. r =  resources
   - Expected: nvme_queue_resources_reason(r) equals `nvme-queue-bar0-unmapped`
3. r =  resources
   - Expected: nvme_queue_resources_reason(r) equals `nvme-queue-invalid-doorbell-stride`
4. r =  resources
   - Expected: nvme_queue_pair_from_resources(r).unwrap_err() equals `nvme-queue-sq-phys-unaligned`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = _resources()
r.depth = 0u16
expect(nvme_queue_resources_reason(r)).to_equal("nvme-queue-depth-zero")

r = _resources()
r.bar0_virt = 0u64
expect(nvme_queue_resources_reason(r)).to_equal("nvme-queue-bar0-unmapped")

r = _resources()
r.doorbell_stride_bytes = 3u32
expect(nvme_queue_resources_reason(r)).to_equal("nvme-queue-invalid-doorbell-stride")

r = _resources()
r.sq_phys = 0x200020u64
expect(nvme_queue_pair_from_resources(r).unwrap_err()).to_equal("nvme-queue-sq-phys-unaligned")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/drivers/nvme/nvme_queue_resources_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- NVMe queue resources

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
