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
| Updated | 2026-08-26 |
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
   - Expected: NvmeBlockAdapter.lease_sector_count_for_test(lease) equals `512u64`
   - Expected: NvmeBlockAdapter.translate_lease_lba_for_test(lease, 0u64).unwrap() equals `1024u64`
   - Expected: NvmeBlockAdapter.translate_lease_lba_for_test(lease, 511u64).unwrap() equals `1535u64`
   - Expected: NvmeBlockAdapter.translate_lease_lba_for_test(lease, 512u64).unwrap_err() equals `nvme-fs-lease-lba-out-of-range`


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
expect(NvmeBlockAdapter.lease_sector_count_for_test(lease)).to_equal(512u64)
expect(NvmeBlockAdapter.translate_lease_lba_for_test(lease, 0u64).unwrap()).to_equal(1024u64)
expect(NvmeBlockAdapter.translate_lease_lba_for_test(lease, 511u64).unwrap()).to_equal(1535u64)
expect(NvmeBlockAdapter.translate_lease_lba_for_test(lease, 512u64).unwrap_err()).to_equal("nvme-fs-lease-lba-out-of-range")
```

</details>

#### rejects hardware adapters for namespaces not identified by the driver

- rejects hardware adapters for namespaces not identified by the driver
   - Expected: adapter.unwrap_err() equals `NvmeBlockAdapter: namespace not identified by driver`


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
expect(adapter.unwrap_err()).to_equal("NvmeBlockAdapter: namespace not identified by driver")
```

</details>

#### enforces the lease window used by filesystem-facing BlockDevice sector IO

- enforces the lease window used by filesystem-facing BlockDevice sector IO
   - Expected: adapter.sector_count() equals `4u64`
   - Expected: adapter.filesystem_consumer() equals `fat32`
   - Expected: adapter.sector_io_absolute_lba_for_test(0u64).unwrap() equals `128u64`
   - Expected: adapter.sector_io_absolute_lba_for_test(3u64).unwrap() equals `131u64`
   - Expected: adapter.sector_io_absolute_lba_for_test(4u64).unwrap_err() equals `NvmeBlockAdapter: lba beyond filesystem lease`


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

expect(adapter.sector_count()).to_equal(4u64)
expect(adapter.filesystem_consumer()).to_equal("fat32")
expect(adapter.sector_io_absolute_lba_for_test(0u64).unwrap()).to_equal(128u64)
expect(adapter.sector_io_absolute_lba_for_test(3u64).unwrap()).to_equal(131u64)
expect(adapter.sector_io_absolute_lba_for_test(4u64).unwrap_err()).to_equal("NvmeBlockAdapter: lba beyond filesystem lease")
```

</details>

#### rejects single and batched 4K DirectIo that would cross the filesystem lease

- rejects single and batched 4K DirectIo that would cross the filesystem lease
   - Expected: adapter.direct_4k_relative_lba_for_test(0i64).unwrap() equals `0u64`
   - Expected: adapter.direct_4k_relative_lba_for_test(512i64).unwrap_err() equals `FsError.InvalidArg`
   - Expected: adapter.direct_4k_relative_lba_for_test(4096i64).unwrap_err() equals `FsError.InvalidArg`


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

expect(adapter.direct_4k_relative_lba_for_test(0i64).unwrap()).to_equal(0u64)
expect(adapter.direct_4k_relative_lba_for_test(512i64).unwrap_err()).to_equal(FsError.InvalidArg)
expect(adapter.direct_4k_relative_lba_for_test(4096i64).unwrap_err()).to_equal(FsError.InvalidArg)
```

</details>

#### routes lease-backed I/O through namespace-aware driver methods

- routes lease-backed I/O through namespace-aware driver methods
   - Expected: source contains `lease_nsid: lease.namespace_identity.nsid`
   - Expected: source contains `lease_queue_id: lease.queue.queue_id`
   - Expected: source contains `identified_sector_count.unwrap() != lease.namespace_identity.lba_count`
   - Expected: source contains `identified_sector_size.unwrap() != lease.namespace_identity.lba_size`
   - Expected: source contains `fn sector_io_absolute_lba_for_test(lba: u64) -> Result<u64, text>:`
   - Expected: source contains `self.nvme.read_sectors_in_namespace_on_queue(self.lease_nsid, self.lease_queu... (full value in folded executable source)`
   - Expected: source contains `self.nvme.write_sectors_in_namespace_on_queue(self.lease_nsid, self.lease_que... (full value in folded executable source)`
   - Expected: source contains `me flush_lease_queue() -> Result<bool, text>:`
   - Expected: source contains `self.nvme.flush_in_namespace_on_queue(self.lease_nsid, self.lease_queue_id)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes lease-backed I/O through namespace-aware driver methods")
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

- exposes a 4K shared-DMA fast path for production random I/O
   - Expected: source contains `me read_4k_shared_dma(relative_lba: u64, buf: SharedDmaBuffer)`
   - Expected: source contains `me write_4k_shared_dma(relative_lba: u64, buf: SharedDmaBuffer)`
   - Expected: source contains `self.nvme.read_4k_shared_dma_burst_in_namespace_on_queue(self.lease_nsid, sel... (full value in folded executable source)`
   - Expected: source contains `self.nvme.write_4k_shared_dma_burst_in_namespace_on_queue(self.lease_nsid, se... (full value in folded executable source)`
   - Expected: source contains `me read_4k_shared_dma_batch(relative_lbas: [u64], buf: SharedDmaBuffer)`
   - Expected: source contains `me write_4k_shared_dma_batch(relative_lbas: [u64], buf: SharedDmaBuffer)`
   - Expected: source contains `self.nvme.read_4k_shared_dma_batch_in_namespace_on_queue(self.lease_nsid, sel... (full value in folded executable source)`
   - Expected: source contains `self.nvme.write_4k_shared_dma_batch_in_namespace_on_queue(self.lease_nsid, se... (full value in folded executable source)`
   - Expected: source does not contain `submit_direct_4k_shared_dma_batch_for_identified_namespace`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exposes a 4K shared-DMA fast path for production random I/O")
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

- bridges the common DirectIo request model to the NVMe 4K shared-DMA path
   - Expected: source contains `use std.fs_driver.direct_io.{DirectIoRequest, DirectIoResult`
   - Expected: source contains `fn direct_4k_extension() -> DirectIoExt`
   - Expected: source contains `backend_tag: "simpleos-nvme-lease-shared-dma-4k"`
   - Expected: source contains `bounce_allowed: false`
   - Expected: source contains `me submit_direct_4k_shared_dma(req: DirectIoRequest) -> Result<DirectIoResult... (full value in folded executable source)`
   - Expected: source contains `val valid = ext.validate_shared_buffer(req.file_offset, req.buffer)`
   - Expected: source contains `val relative_lba = self.direct_4k_relative_lba(req.file_offset)`
   - Expected: source contains `self.read_4k_shared_dma(relative_lba.unwrap(), req.buffer)`
   - Expected: source contains `self.write_4k_shared_dma(relative_lba.unwrap(), req.buffer)`
   - Expected: source contains `buffered_copy_bytes: 0u64`
   - Expected: source contains `direct_dma_copy_bytes: 0u64`
   - Expected: source contains `durable: false`
   - Expected: source contains `me submit_direct_4k_shared_dma_write_through(req: DirectIoRequest) -> Result<... (full value in folded executable source)`
   - Expected: source contains `val flush = self.flush_lease_queue()`
   - Expected: source contains `status: "submitted-flushed"`
   - Expected: source contains `durable: true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bridges the common DirectIo request model to the NVMe 4K shared-DMA path")
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

- bridges batched DirectIo requests to the lease queue for filesystem random I/O
   - Expected: source contains `DirectIoBatchRequest`
   - Expected: source contains `fn direct_4k_batch_extension() -> DirectIoExt`
   - Expected: source contains `backend_tag: "simpleos-nvme-lease-shared-dma-4k-batch"`
   - Expected: source contains `me submit_direct_4k_shared_dma_batch(req: DirectIoBatchRequest) -> Result<Dir... (full value in folded executable source)`
   - Expected: source contains `direct_io_validate_batch(ext, req, 4096u64)`
   - Expected: source contains `val relative_lba = self.direct_4k_relative_lba(offset)`
   - Expected: source contains `bytes: expected_bytes.unwrap()`
   - Expected: source contains `self.read_4k_shared_dma_batch(relative_lbas, req.buffer)`
   - Expected: source contains `self.write_4k_shared_dma_batch(relative_lbas, req.buffer)`
   - Expected: source contains `me submit_direct_4k_shared_dma_batch_write_through(req: DirectIoBatchRequest)... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bridges batched DirectIo requests to the lease queue for filesystem random I/O")
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

- keeps the production pure adapter free of C bridge externs
   - Expected: pure_source does not contain `simpleos_nvme_init`
   - Expected: pure_source does not contain `simpleos_nvme_read_sector`
   - Expected: pure_source does not contain `simpleos_fat32_read_path`
   - Expected: pure_source does not contain `class CNvmeBlockAdapter`
   - Expected: c_source contains `class CNvmeBlockAdapter`
   - Expected: c_source contains `extern fn simpleos_nvme_init() -> i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the production pure adapter free of C bridge externs")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1b9a235218814e960ad3b96b609668bb515970d34c8b4fdedc60a28062ef1892`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1b9a235218814e960ad3b96b609668bb515970d34c8b4fdedc60a28062ef1892`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1b9a235218814e960ad3b96b609668bb515970d34c8b4fdedc60a28062ef1892`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/os/services/vfs/nvme_block_adapter_spec.spl
mirror: doc/06_spec/unit/os/services/vfs/nvme_block_adapter_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/unit/os/services/vfs/nvme_block_adapter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/services/vfs/nvme_block_adapter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/services/vfs/nvme_block_adapter_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
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
