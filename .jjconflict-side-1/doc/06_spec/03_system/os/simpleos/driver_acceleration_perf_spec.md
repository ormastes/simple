# Driver Acceleration Perf Specification

> <details>

<!-- sdn-diagram:id=driver_acceleration_perf_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=driver_acceleration_perf_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

driver_acceleration_perf_spec -> std
driver_acceleration_perf_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=driver_acceleration_perf_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Driver Acceleration Perf Specification

## Scenarios

### SimpleOS driver acceleration performance report

#### compares buffered copy with aligned direct DMA on the same payload

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = 4096u64
expect(buffered_file_copy_bytes(payload)).to_equal(4096)
expect(direct_dma_copy_bytes(payload, true, true)).to_equal(0)
expect(direct_dma_copy_bytes(payload, false, true)).to_equal(4096)
```

</details>

#### compares full-frame and dirty-rectangle display flush cost

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val full = full_frame_flush_bytes(1024, 768, 4)
val dirty = dirty_rect_flush_bytes(1024, 768, 16, 32, 64, 32, 4)
expect(full).to_equal(3145728)
expect(dirty).to_equal(8192)
expect(full).to_be_greater_than(dirty)
```

</details>

#### records backend capability, isolation mode, and RSS fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = build_driver_acceleration_report(
    "virtio-gpu-dma",
    "trusted-driver/no-iommu",
    true,
    4096,
    true,
    true,
    1024,
    768,
    16,
    32,
    64,
    32,
    240,
    104857600,
    65536
)
expect(report.backend_kind).to_equal("virtio-gpu-dma")
expect(report.isolation_mode).to_equal("trusted-driver/no-iommu")
expect(report.network_descriptor_compatible).to_equal(true)
expect(report.buffered_copy_bytes).to_equal(4096)
expect(report.direct_dma_copy_bytes).to_equal(0)
expect(report.dirty_rect_flush_bytes).to_equal(8192)
expect(report.max_rss_kib).to_equal(65536)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/simpleos/driver_acceleration_perf_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS driver acceleration performance report

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
