# File Driver Specification

> <details>

<!-- sdn-diagram:id=file_driver_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=file_driver_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

file_driver_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=file_driver_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# File Driver Specification

## Scenarios

### SOSIX reference file driver on the host filesystem

#### writes bytes through the ring and reads the same bytes back through the ring

- Register a host path and a source buffer with the driver
- Write the buffer at offset 0 with one synchronous wait
   - Expected: written.outcome equals `SOSIX_SYNC_WAIT_COMPLETED`
   - Expected: written.waits equals `1u64`
   - Expected: written.completion.transferred equals `19u64`
   - Expected: written.error.kind equals `0u8`
- Read the middle word back at file offset 8 into a fresh buffer
   - Expected: read.outcome equals `SOSIX_SYNC_WAIT_COMPLETED`
   - Expected: read.completion.transferred equals `5u64`
   - Expected: driver.buffer_bytes(sink) equals `sosix`
- Both operations retired their leases: the ring is empty again
   - Expected: driver.services equals `2u64`
   - Expected: fs.telemetry().completions equals `2u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SOSIX-FS-HOST-FILE
step("Register a host path and a source buffer with the driver")
val fs = setup_sosix_hosted_fs()
val driver = SosixHostedFileDriver.create()
val file = driver.open_path(scratch_path("roundtrip"))
val source = driver.buffer_from("unified sosix bytes")
step("Write the buffer at offset 0 with one synchronous wait")
val written = sosix_sync_fs_write_at(fs, driver, file, source, 0u64, 0u64, 19u64, 0u64)
expect(written.outcome).to_equal(SOSIX_SYNC_WAIT_COMPLETED)
expect(written.waits).to_equal(1u64)
expect(written.completion.transferred).to_equal(19u64)
expect(written.error.kind).to_equal(0u8)
step("Read the middle word back at file offset 8 into a fresh buffer")
val sink = driver.buffer_from("")
val read = sosix_sync_fs_read_at(fs, driver, file, sink, 8u64, 0u64, 5u64, 0u64)
expect(read.outcome).to_equal(SOSIX_SYNC_WAIT_COMPLETED)
expect(read.completion.transferred).to_equal(5u64)
expect(driver.buffer_bytes(sink)).to_equal("sosix")
step("Both operations retired their leases: the ring is empty again")
expect(driver.services).to_equal(2u64)
expect(fs.telemetry().completions).to_equal(2u64)
```

</details>

#### reports a short read past the end of the file as partial progress

- Write five bytes, then ask for sixteen from offset 3
   - Expected: sosix_sync_fs_write_at(fs, driver, file, source, 0u64, 0u64, 5u64, 0u64).outcome equals `SOSIX_SYNC_WAIT_COMPLETED`
- Only the two remaining bytes arrive and the completion says so
   - Expected: read.outcome equals `SOSIX_SYNC_WAIT_COMPLETED`
   - Expected: read.completion.transferred equals `2u64`
   - Expected: read.completion.partial_progress is true
   - Expected: driver.buffer_bytes(sink) equals `de`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Write five bytes, then ask for sixteen from offset 3")
val fs = setup_sosix_hosted_fs()
val driver = SosixHostedFileDriver.create()
val file = driver.open_path(scratch_path("short"))
val source = driver.buffer_from("abcde")
expect(sosix_sync_fs_write_at(fs, driver, file, source, 0u64, 0u64, 5u64, 0u64).outcome).to_equal(SOSIX_SYNC_WAIT_COMPLETED)
val sink = driver.buffer_from("")
val read = sosix_sync_fs_read_at(fs, driver, file, sink, 3u64, 0u64, 16u64, 0u64)
step("Only the two remaining bytes arrive and the completion says so")
expect(read.outcome).to_equal(SOSIX_SYNC_WAIT_COMPLETED)
expect(read.completion.transferred).to_equal(2u64)
expect(read.completion.partial_progress).to_equal(true)
expect(driver.buffer_bytes(sink)).to_equal("de")
```

</details>

#### surfaces a missing file as a typed native error after exactly one wait

- Read from a path that does not exist
   - Expected: read.outcome equals `SOSIX_SYNC_WAIT_COMPLETED`
   - Expected: read.waits equals `1u64`
   - Expected: read.error.kind equals `SOSIX_ERROR_NATIVE`
   - Expected: read.error.native_code equals `SOSIX_FILE_DRIVER_STATUS_IO`
   - Expected: driver.buffer_bytes(sink) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read from a path that does not exist")
val fs = setup_sosix_hosted_fs()
val driver = SosixHostedFileDriver.create()
val file = driver.open_path(scratch_path("does_not_exist_") + "nope")
val sink = driver.buffer_from("")
val read = sosix_sync_fs_read_at(fs, driver, file, sink, 0u64, 0u64, 4u64, 0u64)
expect(read.outcome).to_equal(SOSIX_SYNC_WAIT_COMPLETED)
expect(read.waits).to_equal(1u64)
expect(read.error.kind).to_equal(SOSIX_ERROR_NATIVE)
expect(read.error.native_code).to_equal(SOSIX_FILE_DRIVER_STATUS_IO)
expect(driver.buffer_bytes(sink)).to_equal("")
```

</details>

#### refuses a write whose buffer window starts past the buffer end without touching the file

- Ask to write 4 bytes from offset 10 of a 5-byte buffer
   - Expected: written.outcome equals `SOSIX_SYNC_WAIT_COMPLETED`
   - Expected: written.error.kind equals `SOSIX_ERROR_NATIVE`
   - Expected: written.completion.transferred equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Ask to write 4 bytes from offset 10 of a 5-byte buffer")
val fs = setup_sosix_hosted_fs()
val driver = SosixHostedFileDriver.create()
val file = driver.open_path(scratch_path("window"))
val source = driver.buffer_from("abcde")
val written = sosix_sync_fs_write_at(fs, driver, file, source, 0u64, 10u64, 4u64, 0u64)
expect(written.outcome).to_equal(SOSIX_SYNC_WAIT_COMPLETED)
expect(written.error.kind).to_equal(SOSIX_ERROR_NATIVE)
expect(written.completion.transferred).to_equal(0u64)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/sosix/file_driver_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SOSIX reference file driver on the host filesystem

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

## Generation history

Generated by `simple spipe-docgen` (Simple).
Source SHA-256: `5ac63e26c79a62c014347ff56711a9eccc299896fd3022f5da84f6f7857ef542`
