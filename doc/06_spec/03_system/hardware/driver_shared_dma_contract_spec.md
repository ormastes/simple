# Driver Shared Dma Contract Specification

> <details>

<!-- sdn-diagram:id=driver_shared_dma_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=driver_shared_dma_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

driver_shared_dma_contract_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=driver_shared_dma_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Driver Shared Dma Contract Specification

## Scenarios

### FR-DRIVER-0009 shared DMA descriptor contract

#### canonical descriptor fields

#### network, file, and display consumers use the same descriptor shape

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val network_rx = make_desc(DmaCachePolicy.FlushRequired, 1, 11)
val file_direct = make_desc(DmaCachePolicy.Uncached, 2, 12)
val display_transfer = make_desc(DmaCachePolicy.WriteCombining, 3, 13)
expect(network_rx.cpu_addr()).to_equal(file_direct.cpu_addr())
expect(network_rx.phys_addr()).to_equal(file_direct.phys_addr())
expect(display_transfer.device_visible_addr()).to_equal(0x2000)
expect(network_rx.matches_bdf(0, 1, 0)).to_equal(true)
expect(file_direct.matches_bdf(0, 2, 0)).to_equal(true)
expect(display_transfer.matches_bdf(0, 3, 0)).to_equal(true)
```

</details>

#### all explicit cache policy variants remain representable

1. dma shared sync cpu to device
2. dma shared sync device to cpu
   - Expected: coherent.is_valid() is true
   - Expected: flush_required.is_valid() is true
   - Expected: uncached.is_valid() is true
   - Expected: write_combining.is_valid() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val coherent = make_desc(DmaCachePolicy.Coherent, 4, 20)
val flush_required = make_desc(DmaCachePolicy.FlushRequired, 4, 21)
val uncached = make_desc(DmaCachePolicy.Uncached, 4, 22)
val write_combining = make_desc(DmaCachePolicy.WriteCombining, 4, 23)
dma_shared_sync_cpu_to_device(coherent)
dma_shared_sync_device_to_cpu(flush_required)
expect(coherent.is_valid()).to_equal(true)
expect(flush_required.is_valid()).to_equal(true)
expect(uncached.is_valid()).to_equal(true)
expect(write_combining.is_valid()).to_equal(true)
```

</details>

#### release authority

#### accepts release only for matching task, BDF, size, and allocation id

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val desc = make_desc(DmaCachePolicy.Coherent, 5, 30)
val req = make_release(1024, 7, 5, 30, false)
expect(validate_shared_dma_release(desc, req).is_ok()).to_equal(true)
```

</details>

#### rejects double-free, wrong-size free, and wrong-owner free

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val desc = make_desc(DmaCachePolicy.Coherent, 5, 30)
expect(validate_shared_dma_release(desc, make_release(1024, 7, 5, 30, true)).is_err()).to_equal(true)
expect(validate_shared_dma_release(desc, make_release(512, 7, 5, 30, false)).is_err()).to_equal(true)
expect(validate_shared_dma_release(desc, make_release(1024, 8, 5, 30, false)).is_err()).to_equal(true)
expect(validate_shared_dma_release(desc, make_release(1024, 7, 6, 30, false)).is_err()).to_equal(true)
```

</details>

#### file direct I/O

#### validates std.io.dma.SharedDmaBuffer directly for block/file DMA

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = DirectIoExt(
    sector_alignment: 512,
    file_alignment: 512,
    max_io_bytes: 4096,
    backend_tag: "virtio-blk",
    bounce_allowed: false)
val desc = make_desc(DmaCachePolicy.Uncached, 2, 40)
expect(ext.validate_shared_buffer(1024, desc).is_ok()).to_equal(true)
expect(ext.validate_shared_buffer(7, desc).is_err()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/hardware/driver_shared_dma_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- FR-DRIVER-0009 shared DMA descriptor contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
