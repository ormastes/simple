# Net Shared Dma Ownership Specification

> <details>

<!-- sdn-diagram:id=net_shared_dma_ownership_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=net_shared_dma_ownership_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

net_shared_dma_ownership_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=net_shared_dma_ownership_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Net Shared Dma Ownership Specification

## Scenarios

### FR-NET-0008 shared DMA buffer ownership

#### driver handoff

#### uses SharedDmaBuffer for network packet leases and file direct I/O

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dma = make_dma(4, DmaCachePolicy.FlushRequired, 77)
val rx = packet_rx_dma_lease(1u64, dma)
val tx = packet_tx_dma_lease(1u64, dma)
val ext = DirectIoExt(
    sector_alignment: 512,
    file_alignment: 512,
    max_io_bytes: 4096,
    backend_tag: "virtio-blk",
    bounce_allowed: false)
expect(rx.buffer.allocation_id).to_equal(77)
expect(tx.buffer.len()).to_equal(1024)
expect(ext.validate_shared_buffer(1024, dma).is_ok()).to_equal(true)
```

</details>

#### represents display transfer buffers with the same shared descriptor

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val display = make_dma(2, DmaCachePolicy.WriteCombining, 77)
expect(display.cpu_addr()).to_equal(0x1000)
expect(display.phys_addr()).to_equal(0x2000)
expect(display.device_visible_addr()).to_equal(0x2000)
expect(display.matches_bdf(0, 2, 0)).to_equal(true)
```

</details>

#### release and cache policy

#### rejects double-free and wrong-size release through the shared contract

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dma = make_dma(4, DmaCachePolicy.Coherent, 77)
expect(validate_shared_dma_release(dma, release_req(4, 1024, false)).is_ok()).to_equal(true)
expect(validate_shared_dma_release(dma, release_req(4, 1024, true)).is_err()).to_equal(true)
expect(validate_shared_dma_release(dma, release_req(4, 512, false)).is_err()).to_equal(true)
```

</details>

#### keeps cache maintenance explicit during packet completion

1. dma shared sync cpu to device
2. dma shared sync device to cpu
   - Expected: done.owner equals `driver`
   - Expected: done.completed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dma = make_dma(4, DmaCachePolicy.FlushRequired, 77)
val rx = packet_rx_dma_lease(1u64, dma)
dma_shared_sync_cpu_to_device(rx.buffer)
dma_shared_sync_device_to_cpu(rx.buffer)
val done = packet_dma_complete(rx)
expect(done.owner).to_equal("driver")
expect(done.completed).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/net_shared_dma_ownership_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- FR-NET-0008 shared DMA buffer ownership

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
