# Nvme Filesystem Mounts Specification

> <details>

<!-- sdn-diagram:id=nvme_filesystem_mounts_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=nvme_filesystem_mounts_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

nvme_filesystem_mounts_spec -> std
nvme_filesystem_mounts_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=nvme_filesystem_mounts_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nvme Filesystem Mounts Specification

## Scenarios

### NVMe filesystem mount factory

#### reports the lease region block count used by device-backed filesystems

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lease = _mount_test_lease()
expect(vfs_nvme_filesystem_region_blocks(lease)).to_equal(1024i64)
```

</details>

#### builds FAT32 from the shared lease-backed BlockDevice surface

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lease = _mount_test_lease()
val fat = vfs_nvme_driver_instance_for_lease("fat32-root", MemBlockDevice.new(1024u64, 512u32), lease, NvmeFilesystemConsumer.Fat32)
expect(fat.is_ok()).to_equal(true)
val driver = fat.unwrap()
expect(driver.driver_name()).to_equal("fat32-root")
match driver.probe(Capability.DirectIo):
    case Some(Extension.DirectIo(ext)):
        expect(ext.backend_tag).to_equal("simpleos-nvme-fs-direct-io:fat32")
        expect(ext.bounce_allowed).to_equal(false)
    case _:
        fail("FAT32 NVMe driver did not expose DirectIo extension")
```

</details>

#### keeps arbitrary BlockDevice user mounts buffered unless hardware registered an NVMe adapter

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lease = _user_mount_test_lease(12u32)
val fat = vfs_nvme_buffered_driver_instance_for_lease("user-fat", MemBlockDevice.new(1024u64, 512u32), lease, NvmeFilesystemConsumer.Fat32).unwrap()
val nvfs = vfs_nvme_buffered_driver_instance_for_lease("user-nvfs", MemBlockDevice.new(1024u64, 512u32), lease, NvmeFilesystemConsumer.Nvfs).unwrap()
val dbfs = vfs_nvme_buffered_driver_instance_for_lease("user-dbfs", MemBlockDevice.new(1024u64, 512u32), lease, NvmeFilesystemConsumer.Dbfs).unwrap()

expect(fat.probe(Capability.DirectIo).is_none()).to_equal(true)
expect(nvfs.probe(Capability.DirectIo).is_none()).to_equal(true)
expect(dbfs.probe(Capability.DirectIo).is_none()).to_equal(true)
```

</details>

#### requires the production direct factory to receive the matching lease-backed NVMe adapter

1. NvmeDriver new
   - Expected: mounted.is_ok() is true
2. NvmeDriver new
   - Expected: rejected_consumer.unwrap_err() equals `nvme-fs-adapter-consumer-mismatch adapter=nvfs lease=fat32`
3. NvmeDriver new
   - Expected: rejected_window.unwrap_err() equals `nvme-fs-adapter-sector-count-mismatch adapter=512 lease=1024`


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lease = _mount_test_lease()
val adapter = NvmeBlockAdapter.for_identified_namespace_unchecked(
    NvmeDriver.new(),
    9u32,
    SIMPLEOS_NVME_SYSTEM_QUEUE_ID,
    128u64,
    1024u64,
    512u32,
    "fat32"
)
val mounted = vfs_nvme_driver_instance_for_adapter_lease("fat32-root", adapter, lease, NvmeFilesystemConsumer.Fat32)
expect(mounted.is_ok()).to_equal(true)

val wrong_consumer = NvmeBlockAdapter.for_identified_namespace_unchecked(
    NvmeDriver.new(),
    9u32,
    SIMPLEOS_NVME_SYSTEM_QUEUE_ID,
    128u64,
    1024u64,
    512u32,
    "nvfs"
)
val rejected_consumer = vfs_nvme_driver_instance_for_adapter_lease("fat32-root", wrong_consumer, lease, NvmeFilesystemConsumer.Fat32)
expect(rejected_consumer.unwrap_err()).to_equal("nvme-fs-adapter-consumer-mismatch adapter=nvfs lease=fat32")

val wrong_window = NvmeBlockAdapter.for_identified_namespace_unchecked(
    NvmeDriver.new(),
    9u32,
    SIMPLEOS_NVME_SYSTEM_QUEUE_ID,
    128u64,
    512u64,
    512u32,
    "fat32"
)
val rejected_window = vfs_nvme_driver_instance_for_adapter_lease("fat32-root", wrong_window, lease, NvmeFilesystemConsumer.Fat32)
expect(rejected_window.unwrap_err()).to_equal("nvme-fs-adapter-sector-count-mismatch adapter=512 lease=1024")
```

</details>

#### rejects shared BlockDevice surfaces whose sector size does not match the NVMe lease

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lease = _mount_test_lease()
val reason = vfs_nvme_block_device_lease_reason(MemBlockDevice.new(1024u64, 4096u32), lease)
val direct = vfs_nvme_driver_instance_for_lease("fat32-root", MemBlockDevice.new(1024u64, 4096u32), lease, NvmeFilesystemConsumer.Fat32)
val buffered = vfs_nvme_buffered_driver_instance_for_lease("user-dbfs", MemBlockDevice.new(1024u64, 4096u32), lease, NvmeFilesystemConsumer.Dbfs)

expect(reason).to_equal("nvme-fs-block-device-sector-size-mismatch device=4096 lease=512")
expect(direct.unwrap_err()).to_equal("nvme-fs-block-device-sector-size-mismatch device=4096 lease=512")
expect(buffered.unwrap_err()).to_equal("nvme-fs-block-device-sector-size-mismatch device=4096 lease=512")
```

</details>

#### builds NVFS from the shared lease-backed BlockDevice surface

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lease = _mount_test_lease()
val nvfs = vfs_nvme_driver_instance_for_lease("nvfs-root", MemBlockDevice.new(1024u64, 512u32), lease, NvmeFilesystemConsumer.Nvfs)
expect(nvfs.is_ok()).to_equal(true)
val driver = nvfs.unwrap()
expect(driver.driver_name()).to_equal("nvfs-root")
match driver.probe(Capability.DirectIo):
    case Some(Extension.DirectIo(ext)):
        expect(ext.backend_tag).to_equal("simpleos-nvme-fs-direct-io:nvfs")
        expect(ext.bounce_allowed).to_equal(false)
    case _:
        fail("NVFS NVMe driver did not expose DirectIo extension")
```

</details>

#### requires committed NVFS arena bytes before exposing DirectIo extents

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lease = _mount_test_lease()
val nvfs = vfs_nvme_driver_instance_for_lease("nvfs-root", MemBlockDevice.new(1024u64, 512u32), lease, NvmeFilesystemConsumer.Nvfs)
expect(nvfs.is_ok()).to_equal(true)
val driver = nvfs.unwrap()
val handle = driver.open_path(Path(raw: "/hot.dat"), OpenFlags.read_write().with_create())
expect(handle.is_ok()).to_equal(true)
val extent = driver.direct_io_extent_for_handle(handle.unwrap(), 4096i64, 4096u64)
expect(extent.unwrap_err()).to_equal(FsError.Unsupported)
```

</details>

#### builds DBFS from the shared lease-backed BlockDevice surface

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lease = _mount_test_lease()
val dbfs = vfs_nvme_driver_instance_for_lease("dbfs-root", MemBlockDevice.new(1024u64, 512u32), lease, NvmeFilesystemConsumer.Dbfs)
expect(dbfs.is_ok()).to_equal(true)
val driver = dbfs.unwrap()
expect(driver.driver_name()).to_equal("DbFsDriver")
match driver.probe(Capability.DirectIo):
    case Some(Extension.DirectIo(ext)):
        expect(ext.backend_tag).to_equal("simpleos-nvme-fs-direct-io:dbfs")
        expect(ext.bounce_allowed).to_equal(false)
    case _:
        fail("DBFS NVMe driver did not expose DirectIo extension")
```

</details>

#### requires committed DBFS arena bytes before exposing DirectIo extents

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lease = _mount_test_lease()
val dbfs = vfs_nvme_driver_instance_for_lease("dbfs-root", MemBlockDevice.new(1024u64, 512u32), lease, NvmeFilesystemConsumer.Dbfs)
expect(dbfs.is_ok()).to_equal(true)
val driver = dbfs.unwrap()
val handle = driver.open_path(Path(raw: "/hot.db"), OpenFlags.read_write().with_create())
expect(handle.is_ok()).to_equal(true)
expect(driver.direct_io_extent_for_handle(handle.unwrap(), 0i64, 512u64).unwrap_err()).to_equal(FsError.Unsupported)
```

</details>

#### persists DBFS normal writes through the raw NVMe arena on device-backed mounts

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val driver_source = read_file("src/lib/nogc_sync_mut/db/dbfs_driver/dbfs_driver.spl")
val nvfs_source = read_file("src/lib/nogc_sync_mut/fs_driver/nvfs_driver.spl")
val arena_source = read_file("src/lib/nogc_sync_mut/db/dbfs_engine/raw_nvme_arena.spl")

expect(driver_source.contains("fn _commit_inode_bytes_to_device(inode_id: u64, data: [u8]) -> Result<bool, FsError>:")).to_equal(true)
expect(driver_source.contains("if self.direct_io.is_none():\n            return Ok(false)")).to_equal(true)
expect(driver_source.contains("val handle = arena.arena_handle()\n        val r = arena.arena_append(handle, data, DurabilityClass.BestEffort)")).to_equal(true)
expect(driver_source.contains("_dbfs_record_device_blob(self.inst_id, inode_id, offset, r.bytes_written)")).to_equal(true)
expect(driver_source.contains("val storage_offset = blob_offset + file_offset")).to_equal(true)
expect(driver_source.contains("val bytes = arena.arena_read_bytes(handle, _dbfs_device_blob_offsets[blob_idx], want)")).to_equal(true)
expect(driver_source.contains("val committed = self._commit_inode_bytes_to_device(old.id, _dbfs_slice_bytes(content, content.len() as i64))")).to_equal(true)
expect(driver_source.contains("if committed.is_err():\n            return Ok(())")).to_equal(true)
expect(driver_source.contains("val committed = self._commit_inode_bytes_to_device(old.id, _dbfs_text_to_bytes(new_content))")).to_equal(true)
expect(nvfs_source.contains("self.inner.pwrite_handle(handle, content, offset)?")).to_equal(true)
expect(arena_source.contains("var _nvm_mirror_idxs: [i32]")).to_equal(true)
expect(arena_source.contains("_nvm_mirror_secs.push(sector_copy)")).to_equal(true)
```

</details>

#### round-trips DBFS DirectIo-backed normal bytes from the raw NVMe arena

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val direct = direct_io_nvme_filesystem_extension("dbfs", 512u32)
val opened = DbFsDriver.open_on_device_with_direct_io(MemBlockDevice.new(1024u64, 512u32), 256i64, 128i64, direct)
expect(opened.is_ok()).to_equal(true)
val driver = opened.unwrap()
val handle = driver.open_path(Path(raw: "/arena.db"), OpenFlags.read_write().with_create())
expect(handle.is_ok()).to_equal(true)
val write = driver.write_bytes_handle(handle.unwrap(), [0x44u8, 0x42u8, 0x46u8, 0x53u8])
expect(write.is_ok()).to_equal(true)
val read = driver.read_bytes_handle(handle.unwrap(), 4i64)
expect(read.is_ok()).to_equal(true)
val bytes = read.unwrap()
expect(bytes.len()).to_equal(4)
expect(bytes[0]).to_equal(0x44u8)
expect(bytes[3]).to_equal(0x53u8)
```

</details>

#### does not reuse stale DBFS DirectIo arena sectors across fresh devices

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val direct = direct_io_nvme_filesystem_extension("dbfs", 512u32)
val first = DbFsDriver.open_on_device_with_direct_io(MemBlockDevice.new(1024u64, 512u32), 384i64, 128i64, direct)
expect(first.is_ok()).to_equal(true)
val first_driver = first.unwrap()
val first_handle = first_driver.open_path(Path(raw: "/arena.db"), OpenFlags.read_write().with_create())
expect(first_handle.is_ok()).to_equal(true)
expect(first_driver.write_bytes_handle(first_handle.unwrap(), [0x41u8, 0x41u8, 0x41u8, 0x41u8]).is_ok()).to_equal(true)

val second = DbFsDriver.open_on_device_with_direct_io(MemBlockDevice.new(1024u64, 512u32), 384i64, 128i64, direct)
expect(second.is_ok()).to_equal(true)
val second_driver = second.unwrap()
val second_handle = second_driver.open_path(Path(raw: "/arena.db"), OpenFlags.read_write().with_create())
expect(second_handle.is_ok()).to_equal(true)
expect(second_driver.write_bytes_handle(second_handle.unwrap(), [0x42u8, 0x42u8, 0x42u8, 0x42u8]).is_ok()).to_equal(true)
val second_read = second_driver.read_bytes_handle(second_handle.unwrap(), 4i64)
expect(second_read.is_ok()).to_equal(true)
val second_bytes = second_read.unwrap()
expect(second_bytes.len()).to_equal(4)
expect(second_bytes[0]).to_equal(0x42u8)
expect(second_bytes[3]).to_equal(0x42u8)
```

</details>

#### keeps FAT32 direct I/O extent mapping tied to cluster-chain storage sectors

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val factory = read_file("src/os/services/vfs/nvme_filesystem_mounts.spl")
val stub = read_file("src/lib/nogc_sync_mut/fs_driver/fat32_stub.spl")
val core = read_file("src/lib/nogc_sync_mut/fs_driver/fat32_core.spl")
val async_core = read_file("src/lib/nogc_async_mut/fs_driver/fat32_core.spl")

expect(factory.contains("FsFat32Driver.new_with_direct_io(")).to_equal(true)
expect(factory.contains("direct_io_nvme_filesystem_extension(\"fat32\", lease.namespace_identity.lba_size)")).to_equal(true)
expect(stub.contains("if self.direct_io.is_none():\n            return Err(FsError.Unsupported)")).to_equal(true)
expect(stub.contains("val extent = self.inner.direct_io_extent_for_handle(handle, file_offset, byte_len)")).to_equal(true)
expect(core.contains("me fn direct_io_extent_for_handle(handle: FileHandle, file_offset: i64, byte_len: u64) -> Result<DirectIoExtent, text>:")).to_equal(true)
expect(core.contains("val chain_rc = self.follow_chain(of.start_cluster)")).to_equal(true)
expect(core.contains("val storage_lba = self.cluster_to_sector(chain[cluster_index]) + (offset_in_cluster / sector_size).to_u64()")).to_equal(true)
expect(core.contains("return Err(\"direct I/O range crosses FAT32 cluster\")")).to_equal(true)
expect(async_core.contains("val chain_rc = self.follow_chain(of.start_cluster)")).to_equal(true)
expect(async_core.contains("val storage_lba = self.cluster_to_sector(chain[cluster_index]) + (offset_in_cluster / sector_size).to_u64()")).to_equal(true)
```

</details>

#### rejects consumers when the lease is not filesystem-ready

<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ns = NvmeNamespaceIdentity(
    controller_id: 0,
    nsid: 10,
    lba_size: 512,
    lba_count: 4096,
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
    nsid: 10,
    owner_task: 0,
    max_depth: 128,
    rights: CAP_RIGHT_READ + CAP_RIGHT_WRITE + CAP_RIGHT_QUEUE_SUBMIT
)
val lease = nvme_filesystem_lease(ns, 0u64, 1024u64, NvmeNamespaceMode.System, queue, "simple-driver", "none", false, true)
val result = vfs_nvme_driver_instance_for_lease("bad", MemBlockDevice.new(1024u64, 512u32), lease, NvmeFilesystemConsumer.Fat32)
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err()).to_equal("nvme-fs-lease-missing-shared-block-interface")
```

</details>

#### rejects checked mounts that would mix system and user ownership of one namespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val system_lease = _mount_test_lease()
val user_lease = _user_mount_test_lease(9u32)
val result = vfs_nvme_driver_instance_for_lease_checked("user-fat", MemBlockDevice.new(1024u64, 512u32), user_lease, NvmeFilesystemConsumer.Fat32, [system_lease])
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err()).to_equal("nvme-fs-namespace-mode-conflict:system:user-assigned")
```

</details>

#### accepts checked mounts for different NVMe namespaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val system_lease = _mount_test_lease()
val user_lease = _user_mount_test_lease(11u32)
val result = vfs_nvme_driver_instance_for_lease_checked("user-fat", MemBlockDevice.new(1024u64, 512u32), user_lease, NvmeFilesystemConsumer.Fat32, [system_lease])
expect(result.is_ok()).to_equal(true)
```

</details>

#### mounts root through the checked NVMe lease entry point

1.  clear vfs rootfs for test
   - Expected: result.is_ok() is true
2.  clear vfs rootfs for test


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_clear_vfs_rootfs_for_test()
val lease = _mount_test_lease()
val result = vfs_mount_rootfs_from_nvme_lease_checked("fat32-root", MemBlockDevice.new(1024u64, 512u32), lease, NvmeFilesystemConsumer.Fat32, [])
expect(result.is_ok()).to_equal(true)
_clear_vfs_rootfs_for_test()
```

</details>

#### rejects root mounts that would mix system and user ownership of one namespace

1.  clear vfs rootfs for test
   - Expected: result.is_err() is true
   - Expected: result.unwrap_err() equals `nvme-fs-namespace-mode-conflict:system:user-assigned`
2.  clear vfs rootfs for test


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_clear_vfs_rootfs_for_test()
val system_lease = _mount_test_lease()
val user_lease = _user_mount_test_lease(9u32)
val result = vfs_mount_rootfs_from_nvme_lease_checked("user-fat", MemBlockDevice.new(1024u64, 512u32), user_lease, NvmeFilesystemConsumer.Fat32, [system_lease])
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err()).to_equal("nvme-fs-namespace-mode-conflict:system:user-assigned")
_clear_vfs_rootfs_for_test()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/services/vfs/nvme_filesystem_mounts_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- NVMe filesystem mount factory

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
