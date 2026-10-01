# NVMe Block Adapter Lease Specification

> Regression coverage for the filesystem-facing pure Simple NVMe adapter. These

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
| Source | `test/unit/os/services/vfs/nvme_block_adapter_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

Regression coverage for the filesystem-facing pure Simple NVMe adapter. These
tests avoid real hardware and prove that adapter-visible helpers preserve the
same bounded namespace window used by FAT32, NVFS, and DBFS.

## Scenarios

### NVMe VFS block adapter lease helpers

#### translates filesystem-relative LBAs through the shared lease window

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- translates filesystem-relative LBAs through the shared lease window


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("translates filesystem-relative LBAs through the shared lease window")
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
assert_equal(NvmeBlockAdapter.lease_sector_count_for_test(lease), 512u64)
assert_equal(NvmeBlockAdapter.translate_lease_lba_for_test(lease, 0u64).unwrap(), 1024u64)
assert_equal(NvmeBlockAdapter.translate_lease_lba_for_test(lease, 511u64).unwrap(), 1535u64)
assert_equal(NvmeBlockAdapter.translate_lease_lba_for_test(lease, 512u64).unwrap_err(), "nvme-fs-lease-lba-out-of-range")
```

</details>

#### rejects hardware adapters for namespaces not identified by the driver

- rejects hardware adapters for namespaces not identified by the driver


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects hardware adapters for namespaces not identified by the driver")
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
assert_equal(adapter.unwrap_err(), "NvmeBlockAdapter: namespace not identified by driver")
```

</details>

#### enforces the lease window used by filesystem-facing BlockDevice sector IO

- enforces the lease window used by filesystem-facing BlockDevice sector IO


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enforces the lease window used by filesystem-facing BlockDevice sector IO")
val adapter = NvmeBlockAdapter.for_identified_namespace_unchecked(
    NvmeDriver.new(),
    7u32,
    SIMPLEOS_NVME_SYSTEM_QUEUE_ID,
    128u64,
    4u64,
    512u32,
    "fat32"
)

assert_equal(adapter.sector_count(), 4u64)
assert_equal(adapter.filesystem_consumer(), "fat32")
assert_equal(adapter.sector_io_absolute_lba_for_test(0u64).unwrap(), 128u64)
assert_equal(adapter.sector_io_absolute_lba_for_test(3u64).unwrap(), 131u64)
assert_equal(adapter.sector_io_absolute_lba_for_test(4u64).unwrap_err(), "NvmeBlockAdapter: lba beyond filesystem lease")
```

</details>

#### rejects single and batched 4K DirectIo that would cross the filesystem lease

- rejects single and batched 4K DirectIo that would cross the filesystem lease


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects single and batched 4K DirectIo that would cross the filesystem lease")
val adapter = NvmeBlockAdapter.for_identified_namespace_unchecked(
    NvmeDriver.new(),
    7u32,
    SIMPLEOS_NVME_SYSTEM_QUEUE_ID,
    128u64,
    8u64,
    512u32,
    "fat32"
)

assert_equal(adapter.direct_4k_relative_lba_for_test(0i64).unwrap(), 0u64)
assert_equal(adapter.direct_4k_relative_lba_for_test(512i64).unwrap_err(), FsError.InvalidArg)
assert_equal(adapter.direct_4k_relative_lba_for_test(4096i64).unwrap_err(), FsError.InvalidArg)
```

</details>

#### routes lease-backed I/O through namespace-aware driver methods

- routes lease-backed I/O through namespace-aware driver methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes lease-backed I/O through namespace-aware driver methods")
val source = read_file("src/os/services/vfs/vfs_block_adapters.spl")
assert_equal(source.contains("lease_nsid: lease.namespace_identity.nsid"), true)
assert_equal(source.contains("lease_queue_id: lease.queue.queue_id"), true)
assert_equal(source.contains("identified_sector_count.unwrap() != lease.namespace_identity.lba_count"), true)
assert_equal(source.contains("identified_sector_size.unwrap() != lease.namespace_identity.lba_size"), true)
assert_equal(source.contains("fn sector_io_absolute_lba_for_test(lba: u64) -> Result<u64, text>:"), true)
assert_equal(source.contains("self.nvme.read_sectors_in_namespace_on_queue(self.lease_nsid, self.lease_queue_id"), true)
assert_equal(source.contains("self.nvme.write_sectors_in_namespace_on_queue(self.lease_nsid, self.lease_queue_id"), true)
assert_equal(source.contains("me flush_lease_queue() -> Result<bool, text>:"), true)
assert_equal(source.contains("self.nvme.flush_in_namespace_on_queue(self.lease_nsid, self.lease_queue_id)"), true)
```

</details>

#### exposes a 4K shared-DMA fast path for production random I/O

- exposes a 4K shared-DMA fast path for production random I/O


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exposes a 4K shared-DMA fast path for production random I/O")
val source = read_file("src/os/services/vfs/vfs_block_adapters.spl")
assert_equal(source.contains("me read_4k_shared_dma(relative_lba: u64, buf: SharedDmaBuffer)"), true)
assert_equal(source.contains("me write_4k_shared_dma(relative_lba: u64, buf: SharedDmaBuffer)"), true)
assert_equal(source.contains("self.nvme.read_4k_shared_dma_burst_in_namespace_on_queue(self.lease_nsid, self.lease_queue_id"), true)
assert_equal(source.contains("self.nvme.write_4k_shared_dma_burst_in_namespace_on_queue(self.lease_nsid, self.lease_queue_id"), true)
assert_equal(source.contains("me read_4k_shared_dma_batch(relative_lbas: [u64], buf: SharedDmaBuffer)"), true)
assert_equal(source.contains("me write_4k_shared_dma_batch(relative_lbas: [u64], buf: SharedDmaBuffer)"), true)
assert_equal(source.contains("self.nvme.read_4k_shared_dma_batch_in_namespace_on_queue(self.lease_nsid, self.lease_queue_id"), true)
assert_equal(source.contains("self.nvme.write_4k_shared_dma_batch_in_namespace_on_queue(self.lease_nsid, self.lease_queue_id"), true)
assert_equal(source.contains("submit_direct_4k_shared_dma_batch_for_identified_namespace"), false)
```

</details>

#### bridges the common DirectIo request model to the NVMe 4K shared-DMA path

- bridges the common DirectIo request model to the NVMe 4K shared-DMA path


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bridges the common DirectIo request model to the NVMe 4K shared-DMA path")
val source = read_file("src/os/services/vfs/vfs_block_adapters.spl")
assert_equal(source.contains("use std.fs_driver.direct_io.{DirectIoRequest, DirectIoResult"), true)
assert_equal(source.contains("fn direct_4k_extension() -> DirectIoExt"), true)
assert_equal(source.contains("backend_tag: \"simpleos-nvme-lease-shared-dma-4k\""), true)
assert_equal(source.contains("bounce_allowed: false"), true)
assert_equal(source.contains("me submit_direct_4k_shared_dma(req: DirectIoRequest) -> Result<DirectIoResult, FsError>"), true)
assert_equal(source.contains("val valid = ext.validate_shared_buffer(req.file_offset, req.buffer)"), true)
assert_equal(source.contains("val relative_lba = self.direct_4k_relative_lba(req.file_offset)"), true)
assert_equal(source.contains("self.read_4k_shared_dma(relative_lba.unwrap(), req.buffer)"), true)
assert_equal(source.contains("self.write_4k_shared_dma(relative_lba.unwrap(), req.buffer)"), true)
assert_equal(source.contains("buffered_copy_bytes: 0u64"), true)
assert_equal(source.contains("direct_dma_copy_bytes: 0u64"), true)
assert_equal(source.contains("durable: false"), true)
assert_equal(source.contains("me submit_direct_4k_shared_dma_write_through(req: DirectIoRequest) -> Result<DirectIoResult, FsError>"), true)
assert_equal(source.contains("val flush = self.flush_lease_queue()"), true)
assert_equal(source.contains("status: \"submitted-flushed\""), true)
assert_equal(source.contains("durable: true"), true)
```

</details>

#### bridges batched DirectIo requests to the lease queue for filesystem random I/O

- bridges batched DirectIo requests to the lease queue for filesystem random I/O


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bridges batched DirectIo requests to the lease queue for filesystem random I/O")
val source = read_file("src/os/services/vfs/vfs_block_adapters.spl")
assert_equal(source.contains("DirectIoBatchRequest"), true)
assert_equal(source.contains("fn direct_4k_batch_extension() -> DirectIoExt"), true)
assert_equal(source.contains("backend_tag: \"simpleos-nvme-lease-shared-dma-4k-batch\""), true)
assert_equal(source.contains("me submit_direct_4k_shared_dma_batch(req: DirectIoBatchRequest) -> Result<DirectIoResult, FsError>"), true)
assert_equal(source.contains("direct_io_validate_batch(ext, req, 4096u64)"), true)
assert_equal(source.contains("val relative_lba = self.direct_4k_relative_lba(offset)"), true)
assert_equal(source.contains("bytes: expected_bytes.unwrap()"), true)
assert_equal(source.contains("self.read_4k_shared_dma_batch(relative_lbas, req.buffer)"), true)
assert_equal(source.contains("self.write_4k_shared_dma_batch(relative_lbas, req.buffer)"), true)
assert_equal(source.contains("me submit_direct_4k_shared_dma_batch_write_through(req: DirectIoBatchRequest) -> Result<DirectIoResult, FsError>"), true)
```

</details>

#### keeps the production pure adapter free of C bridge externs

- keeps the production pure adapter free of C bridge externs


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the production pure adapter free of C bridge externs")
val pure_source = read_file("src/os/services/vfs/vfs_block_adapters.spl")
val c_source = read_file("src/os/services/vfs/c_nvme_block_adapter.spl")

assert_equal(pure_source.contains("simpleos_nvme_init"), false)
assert_equal(pure_source.contains("simpleos_nvme_read_sector"), false)
assert_equal(pure_source.contains("simpleos_fat32_read_path"), false)
assert_equal(pure_source.contains("class CNvmeBlockAdapter"), false)
assert_equal(c_source.contains("class CNvmeBlockAdapter"), true)
assert_equal(c_source.contains("extern fn simpleos_nvme_init() -> i64"), true)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5e7571bf7b1c6c7fbf1672aa46fa2b2a8b1a2b0d148e2c748fc470a5e0bfc7f0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5e7571bf7b1c6c7fbf1672aa46fa2b2a8b1a2b0d148e2c748fc470a5e0bfc7f0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5e7571bf7b1c6c7fbf1672aa46fa2b2a8b1a2b0d148e2c748fc470a5e0bfc7f0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/services/vfs/nvme_block_adapter_spec.spl
mirror: doc/06_spec/unit/os/services/vfs/nvme_block_adapter_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/services/vfs/nvme_block_adapter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/services/vfs/nvme_block_adapter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/services/vfs/nvme_block_adapter_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'translates filesystem-relative LBAs through the shared lease window' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/services/vfs/nvme_block_adapter_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects hardware adapters for namespaces not identified by the driver' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/services/vfs/nvme_block_adapter_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'enforces the lease window used by filesystem-facing BlockDevice sector IO' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
