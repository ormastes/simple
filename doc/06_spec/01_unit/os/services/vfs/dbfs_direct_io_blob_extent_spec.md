# Dbfs Direct Io Blob Extent Specification

> <details>

<!-- sdn-diagram:id=dbfs_direct_io_blob_extent_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dbfs_direct_io_blob_extent_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dbfs_direct_io_blob_extent_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dbfs_direct_io_blob_extent_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dbfs Direct Io Blob Extent Specification

## Scenarios

### DBFS DirectIo blob extent mapping

#### maps DBFS and NVFS extents through committed RawNvmeArena blob offsets

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val direct = direct_io_nvme_filesystem_extension("dbfs", 1u32)
val opened = DbFsDriver.open_on_device_with_direct_io(MemBlockDevice.new(1024u64, 1u32), 512i64, 128i64, direct)
expect(opened.is_ok()).to_equal(true)
val driver = opened.unwrap()
val first = driver.open_path(Path(raw: "/first.db"), OpenFlags.read_write().with_create())
val second = driver.open_path(Path(raw: "/second.db"), OpenFlags.read_write().with_create())
expect(first.is_ok()).to_equal(true)
expect(second.is_ok()).to_equal(true)
expect(driver.write_bytes_handle(first.unwrap(), [0x31u8]).is_ok()).to_equal(true)
expect(driver.write_bytes_handle(second.unwrap(), [0x32u8]).is_ok()).to_equal(true)

val second_extent = driver.direct_io_extent_for_handle(second.unwrap(), 0i64, 1u64).unwrap()
expect(second_extent.consumer).to_equal("dbfs")
expect(second_extent.storage_lba).to_equal(514u64)
expect(second_extent.byte_len).to_equal(1u64)

val nvfs_extent = driver.direct_io_extent_for_consumer(second.unwrap(), 0i64, 1u64, "nvfs").unwrap()
expect(nvfs_extent.consumer).to_equal("nvfs")
expect(nvfs_extent.storage_lba).to_equal(514u64)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/services/vfs/dbfs_direct_io_blob_extent_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DBFS DirectIo blob extent mapping

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
