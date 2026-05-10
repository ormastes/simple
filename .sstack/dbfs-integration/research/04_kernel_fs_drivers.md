# Stream D — Kernel FS + NVMe + Drivers + Boot

**Date:** 2026-04-28

## FAT32 Boot Path (AC-7 Confirmation)

**Kernel FAT32:** `src/os/kernel/fs/fat32.spl`
- Implements: BPB parse + cluster-to-lba arithmetic + `mount()` (wave-4a), `readdir("/")` via root-dir chain (wave-4b), `open()` + `read()` + `stat()` for 8.3 names (wave-4c)
- Types: `FileHandle` (fd/start_cluster/current_cluster/offset/file_size/is_open), `FileStat` (size/is_dir/mtime), `Fat32Bpb`
- Status: **Functional for read-only boot path.** Wave-4a/4b/4c confirmed complete.

**VFS Init:** `src/os/services/vfs/vfs_init.spl`
- Sequence: PCI manager → NVMe init (via C bridge `simpleos_nvme_init`) → FAT32 reads BPB from NVMe → mounts FAT32 at "/" → starts VFS IPC service
- Uses `DriverInstance` and `MountTable` from `std.fs_driver`
- C bridge externs: `simpleos_nvme_read_sector`, `simpleos_fat32_read_path`, etc. (bypass auto-stubbed MMIO)

**DBFS safety:** Boot path uses C bridge FAT32 → DBFS never touches boot. Zero risk to AC-7 as long as DBFS only mounts at `/data` (or named test path) and never touches the "/" mount.

## NVMe Driver Maturity

**Files:** `src/os/drivers/nvme/` (7 files)
- `nvme_driver.spl` — Full NVMe init sequence (8 steps: BAR0 map, CAP read, disable, alloc DMA, configure AQA/ASQ/ACQ, enable, Identify Controller + NS1, create I/O queues). Syscalls 83 (MapBar), 84 (AllocDma), 26 (NotificationWait).
- `nvme_queue.spl` — `NvmeQueuePair` struct with real SQE submission (`submit_command`): builds 64-byte SQE, handles sq_virt/doorbell bounds checks. Phase-bit tracking, doorbell writes.
- `nvme_block_device.spl` — Implements both sync `BlockDevice` and async `AsyncBlockDevice` for `NvmeDriver`. Sync: spin-polling. Async: notification-based (`read_sectors_notify`/`write_sectors_notify`/`flush_notify`). Also `read_shared_dma`/`write_shared_dma` via `SharedDmaBuffer` (DMA sync helpers).
- `block_device.spl`, `nvme_storage_model.spl`, `nvme_async.spl`, `mod.spl`

**Block device trait (OS layer):** `src/os/services/block_device.spl`
```
trait BlockDevice:
    fn read_sector(lba: u64, buffer: [u8]) -> Result<bool, text>
    fn write_sector(lba: u64, data: [u8]) -> Result<bool, text>
    fn sector_size() -> u32
```

**Assessment:** NVMe driver is **production-class**:
- Real MMIO/DMA path with BAR0 mapping and DMA allocation
- Both sync (spin-poll) and async (notification-based IRQ) completion paths
- Full SQE construction with all NVMe command fields
- `SharedDmaBuffer` for caller-owned DMA (direct I/O path exists)
- I/O queue creation and doorbell management implemented

**Maturity rating: HIGH.** End-to-end submission/completion path works. DBFS can plug directly into `BlockDevice` trait for the raw-NVMe backend.

## Virtio Block (Secondary Path)

**File:** `src/os/drivers/virtio/virtio_blk.spl` — VirtioBlkDriver present. DBFS should also work via virtio for QEMU testing without real NVMe hardware.

## VFS Service Layer

**File:** `src/os/services/vfs/vfs_init.spl`
- Uses `MountTable` from `std.fs_driver` — the same library seam DBFS plugs into
- NVFS connector: `src/os/services/vfs/nvfs_connector.spl` — shows how NVFS is connected at the OS service level

## OS Driver Summary

`src/os/drivers/desktop_driver_summary.spl` — exists but not in scope.

## Key Finding for DBFS

The block layer API (`BlockDevice` trait: `read_sector`/`write_sector`/`sector_size`) is the correct plug point for DBFS's `RawNvmeArena`. The driver manifest path through `vfs_init.spl` → `NvmeDriver` → `BlockDevice` is production-ready. DBFS can:
1. Receive a `BlockDevice` implementor at mount time
2. Wrap it in a `RawNvmeArena` that implements the `Arena` trait
3. Mount at `/data` via `MountTable.mount("/data", DriverInstance.DbFs(DbFsDriver.new(arena)), opts)`

No changes to NVMe driver, virtio driver, or boot path required.
