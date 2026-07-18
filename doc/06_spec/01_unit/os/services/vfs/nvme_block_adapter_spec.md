# NVMe Block Adapter Lease Specification

> Regression coverage for the filesystem-facing pure Simple NVMe adapter. These

<!-- sdn-diagram:id=nvme_block_adapter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=nvme_block_adapter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

nvme_block_adapter_spec -> std
nvme_block_adapter_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=nvme_block_adapter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# NVMe Block Adapter Lease Specification

Regression coverage for the filesystem-facing pure Simple NVMe adapter. These

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/services/vfs/nvme_block_adapter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Regression coverage for the filesystem-facing pure Simple NVMe adapter. These
tests avoid real hardware and prove that adapter-visible helpers preserve the
same bounded namespace window used by FAT32, NVFS, and DBFS.

## Scenarios

### NVMe VFS block adapter lease helpers

#### translates filesystem-relative LBAs through the shared lease window

<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ns = NvmeNamespaceIdentity(
    controller_id: 0,
    nsid: 7,
    lba_size: 4096,
    lba_count: 8192,
    eui64: 0,
    nguid_lo: 0,
    nguid_hi: 0,
    uuid_lo: 0,
    uuid_hi: 0
)
val queue = NvmeQueueAssignment(
    queue_id: SIMPLEOS_NVME_SYSTEM_QUEUE_ID,
    role: NvmeQueueRole.System,
    controller_id: 0,
    nsid: 7,
    owner_task: 0,
    max_depth: 128,
    rights: CAP_RIGHT_READ + CAP_RIGHT_WRITE + CAP_RIGHT_QUEUE_SUBMIT
)
val lease = nvme_filesystem_lease(ns, 1024u64, 512u64, NvmeNamespaceMode.System, queue, "simple-driver", "none", true, true)
expect(NvmeBlockAdapter.lease_sector_count_for_test(lease)).to_equal(512u64)
expect(NvmeBlockAdapter.translate_lease_lba_for_test(lease, 0u64).unwrap()).to_equal(1024u64)
expect(NvmeBlockAdapter.translate_lease_lba_for_test(lease, 511u64).unwrap()).to_equal(1535u64)
expect(NvmeBlockAdapter.translate_lease_lba_for_test(lease, 512u64).unwrap_err()).to_equal("nvme-fs-lease-lba-out-of-range")
```

</details>

#### rejects hardware adapters for namespaces not identified by the driver

<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ns = NvmeNamespaceIdentity(
    controller_id: 0,
    nsid: 7,
    lba_size: 4096,
    lba_count: 8192,
    eui64: 0,
    nguid_lo: 0,
    nguid_hi: 0,
    uuid_lo: 0,
    uuid_hi: 0
)
val queue = NvmeQueueAssignment(
    queue_id: SIMPLEOS_NVME_SYSTEM_QUEUE_ID,
    role: NvmeQueueRole.System,
    controller_id: 0,
    nsid: 7,
    owner_task: 0,
    max_depth: 128,
    rights: CAP_RIGHT_READ + CAP_RIGHT_WRITE + CAP_RIGHT_QUEUE_SUBMIT
)
val lease = nvme_filesystem_lease(ns, 0u64, 512u64, NvmeNamespaceMode.System, queue, "simple-driver", "none", true, true)
val adapter = NvmeBlockAdapter.for_filesystem_lease(NvmeDriver.new(), lease, NvmeFilesystemConsumer.Fat32)
expect(adapter.unwrap_err()).to_equal("NvmeBlockAdapter: namespace not identified by driver")
```

</details>

#### enforces the lease window used by filesystem-facing BlockDevice sector IO

1. NvmeDriver new
   - Expected: adapter.sector_count() equals `4u64`
   - Expected: adapter.filesystem_consumer() equals `fat32`
   - Expected: adapter.sector_io_absolute_lba_for_test(0u64).unwrap() equals `128u64`
   - Expected: adapter.sector_io_absolute_lba_for_test(3u64).unwrap() equals `131u64`
   - Expected: adapter.sector_io_absolute_lba_for_test(4u64).unwrap_err() equals `NvmeBlockAdapter: lba beyond filesystem lease`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = NvmeBlockAdapter.for_identified_namespace_unchecked(
    NvmeDriver.new(),
    7u32,
    SIMPLEOS_NVME_SYSTEM_QUEUE_ID,
    128u64,
    4u64,
    512u32,
    "fat32"
)

expect(adapter.sector_count()).to_equal(4u64)
expect(adapter.filesystem_consumer()).to_equal("fat32")
expect(adapter.sector_io_absolute_lba_for_test(0u64).unwrap()).to_equal(128u64)
expect(adapter.sector_io_absolute_lba_for_test(3u64).unwrap()).to_equal(131u64)
expect(adapter.sector_io_absolute_lba_for_test(4u64).unwrap_err()).to_equal("NvmeBlockAdapter: lba beyond filesystem lease")
```

</details>

#### rejects single and batched 4K DirectIo that would cross the filesystem lease

1. NvmeDriver new
   - Expected: adapter.direct_4k_relative_lba_for_test(0i64).unwrap() equals `0u64`
   - Expected: adapter.direct_4k_relative_lba_for_test(512i64).unwrap_err() equals `FsError.InvalidArg`
   - Expected: adapter.direct_4k_relative_lba_for_test(4096i64).unwrap_err() equals `FsError.InvalidArg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = NvmeBlockAdapter.for_identified_namespace_unchecked(
    NvmeDriver.new(),
    7u32,
    SIMPLEOS_NVME_SYSTEM_QUEUE_ID,
    128u64,
    8u64,
    512u32,
    "fat32"
)

expect(adapter.direct_4k_relative_lba_for_test(0i64).unwrap()).to_equal(0u64)
expect(adapter.direct_4k_relative_lba_for_test(512i64).unwrap_err()).to_equal(FsError.InvalidArg)
expect(adapter.direct_4k_relative_lba_for_test(4096i64).unwrap_err()).to_equal(FsError.InvalidArg)
```

</details>

#### routes lease-backed I/O through namespace-aware driver methods

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("src/os/services/vfs/vfs_block_adapters.spl")
expect(source.contains("lease_nsid: lease.namespace_identity.nsid")).to_equal(true)
expect(source.contains("lease_queue_id: lease.queue.queue_id")).to_equal(true)
expect(source.contains("identified_sector_count.unwrap() != lease.namespace_identity.lba_count")).to_equal(true)
expect(source.contains("identified_sector_size.unwrap() != lease.namespace_identity.lba_size")).to_equal(true)
expect(source.contains("fn sector_io_absolute_lba_for_test(lba: u64) -> Result<u64, text>:")).to_equal(true)
expect(source.contains("self.nvme.read_sectors_in_namespace_on_queue(self.lease_nsid, self.lease_queue_id")).to_equal(true)
expect(source.contains("self.nvme.write_sectors_in_namespace_on_queue(self.lease_nsid, self.lease_queue_id")).to_equal(true)
expect(source.contains("me flush_lease_queue() -> Result<bool, text>:")).to_equal(true)
expect(source.contains("self.nvme.flush_in_namespace_on_queue(self.lease_nsid, self.lease_queue_id)")).to_equal(true)
```

</details>

#### exposes a 4K shared-DMA fast path for production random I/O

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("src/os/services/vfs/vfs_block_adapters.spl")
expect(source.contains("me read_4k_shared_dma(relative_lba: u64, buf: SharedDmaBuffer)")).to_equal(true)
expect(source.contains("me write_4k_shared_dma(relative_lba: u64, buf: SharedDmaBuffer)")).to_equal(true)
expect(source.contains("self.nvme.read_4k_shared_dma_burst_in_namespace_on_queue(self.lease_nsid, self.lease_queue_id")).to_equal(true)
expect(source.contains("self.nvme.write_4k_shared_dma_burst_in_namespace_on_queue(self.lease_nsid, self.lease_queue_id")).to_equal(true)
expect(source.contains("me read_4k_shared_dma_batch(relative_lbas: [u64], buf: SharedDmaBuffer)")).to_equal(true)
expect(source.contains("me write_4k_shared_dma_batch(relative_lbas: [u64], buf: SharedDmaBuffer)")).to_equal(true)
expect(source.contains("self.nvme.read_4k_shared_dma_batch_in_namespace_on_queue(self.lease_nsid, self.lease_queue_id")).to_equal(true)
expect(source.contains("self.nvme.write_4k_shared_dma_batch_in_namespace_on_queue(self.lease_nsid, self.lease_queue_id")).to_equal(true)
expect(source.contains("submit_direct_4k_shared_dma_batch_for_identified_namespace")).to_equal(false)
```

</details>

#### bridges the common DirectIo request model to the NVMe 4K shared-DMA path

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("src/os/services/vfs/vfs_block_adapters.spl")
expect(source.contains("use std.fs_driver.direct_io.{DirectIoRequest, DirectIoResult")).to_equal(true)
expect(source.contains("fn direct_4k_extension() -> DirectIoExt")).to_equal(true)
expect(source.contains("backend_tag: \"simpleos-nvme-lease-shared-dma-4k\"")).to_equal(true)
expect(source.contains("bounce_allowed: false")).to_equal(true)
expect(source.contains("me submit_direct_4k_shared_dma(req: DirectIoRequest) -> Result<DirectIoResult, FsError>")).to_equal(true)
expect(source.contains("val valid = ext.validate_shared_buffer(req.file_offset, req.buffer)")).to_equal(true)
expect(source.contains("val relative_lba = self.direct_4k_relative_lba(req.file_offset)")).to_equal(true)
expect(source.contains("self.read_4k_shared_dma(relative_lba.unwrap(), req.buffer)")).to_equal(true)
expect(source.contains("self.write_4k_shared_dma(relative_lba.unwrap(), req.buffer)")).to_equal(true)
expect(source.contains("buffered_copy_bytes: 0u64")).to_equal(true)
expect(source.contains("direct_dma_copy_bytes: 0u64")).to_equal(true)
expect(source.contains("durable: false")).to_equal(true)
expect(source.contains("me submit_direct_4k_shared_dma_write_through(req: DirectIoRequest) -> Result<DirectIoResult, FsError>")).to_equal(true)
expect(source.contains("val flush = self.flush_lease_queue()")).to_equal(true)
expect(source.contains("status: \"submitted-flushed\"")).to_equal(true)
expect(source.contains("durable: true")).to_equal(true)
```

</details>

#### bridges batched DirectIo requests to the lease queue for filesystem random I/O

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("src/os/services/vfs/vfs_block_adapters.spl")
expect(source.contains("DirectIoBatchRequest")).to_equal(true)
expect(source.contains("fn direct_4k_batch_extension() -> DirectIoExt")).to_equal(true)
expect(source.contains("backend_tag: \"simpleos-nvme-lease-shared-dma-4k-batch\"")).to_equal(true)
expect(source.contains("me submit_direct_4k_shared_dma_batch(req: DirectIoBatchRequest) -> Result<DirectIoResult, FsError>")).to_equal(true)
expect(source.contains("direct_io_validate_batch(ext, req, 4096u64)")).to_equal(true)
expect(source.contains("val relative_lba = self.direct_4k_relative_lba(offset)")).to_equal(true)
expect(source.contains("bytes: expected_bytes.unwrap()")).to_equal(true)
expect(source.contains("self.read_4k_shared_dma_batch(relative_lbas, req.buffer)")).to_equal(true)
expect(source.contains("self.write_4k_shared_dma_batch(relative_lbas, req.buffer)")).to_equal(true)
expect(source.contains("me submit_direct_4k_shared_dma_batch_write_through(req: DirectIoBatchRequest) -> Result<DirectIoResult, FsError>")).to_equal(true)
```

</details>

#### keeps the production pure adapter free of C bridge externs

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pure_source = read_file("src/os/services/vfs/vfs_block_adapters.spl")
val c_source = read_file("src/os/services/vfs/c_nvme_block_adapter.spl")

expect(pure_source.contains("simpleos_nvme_init")).to_equal(false)
expect(pure_source.contains("simpleos_nvme_read_sector")).to_equal(false)
expect(pure_source.contains("simpleos_fat32_read_path")).to_equal(false)
expect(pure_source.contains("class CNvmeBlockAdapter")).to_equal(false)
expect(c_source.contains("class CNvmeBlockAdapter")).to_equal(true)
expect(c_source.contains("extern fn simpleos_nvme_init() -> i64")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
