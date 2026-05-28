# NVFS + DBFS: Real NVMe-Backed Filesystem

NVMe-backed NVFS and DBFS filesystems for SimpleOS.
Store files, persist across remounts, load ELF binaries.

## Done

- NVFS arena backed by RawNvmeArena (BlockDevice → NVMe sectors)
- NVFS superblock at LBA 0 with A/B replicas
- DBFS superblock at LBA 2-3 (coexists with NVFS)
- DBFS intent_log + checkpoint_ring wired to BlockDevice
- NVFS name table persistence (sectors 48-63, survives remount)
- DBFS FsDriver (stat/open/read/write/close/mkdir/unlink/rename)
- Boot FS cascade: NVFS → DBFS → FAT32 fallback
- ELF binary load from NVFS arena verified by loader specs
- DBFS mounted-root executable byte loading is binary-safe and verified through VFS resolution plus ELF loader parsing
- Shared BTree<V>, checkpoint_ring, intent_log in storage/shared/
- NVFS fd_table (NvfsFdEntry) wired into NvfsPosixDriver
- Shared WAL extraction (`dbfs_engine/wal.spl` → `storage/shared/wal.spl`)
- Recovery side effects route orphan arena discard IDs and clean checkpoint generation through registered recovery callbacks
- Intent log BlockDevice-backed callback persistence survives reopen
- Checkpoint ring BlockDevice-backed callback persistence survives reopen
- Pager left DBFS-local because only DBFS uses it
- Samsung business NVMe conventional policy wired: 4 KiB physical I/O, 128 KiB DB_WAL batch, discard/write-zeroes support, and FDP/ZNS disabled when sysfs does not advertise them
- Gated DBFS-marked FAT32 carrier image smoke passes at `test/system/os/port/dbfs_disk_boot_spec.spl`
- Hosted DBFS/NVFS rootfs file I/O coverage exists at `test/unit/os/services/vfs/vfs_rootfs_porting_spec.spl`

## Verification

- `bin/simple test test/integration/storage/dbfs/dbfs_engine_wal_spec.spl`
- `bin/simple test test/integration/storage/dbfs/dbfs_nvme_callback_spec.spl`
- `bin/simple test test/integration/storage/dbfs/dbfs_recovery_spec.spl`
- `bin/simple test test/integration/storage/dbfs/samsung_nvme_feature_policy_spec.spl`
- `bin/simple test test/integration/storage/dbfs/bench_harness_smoke_spec.spl`
- `bin/simple test test/integration/storage/dbfs/dbfs_driver_spec.spl`
- `bin/simple test test/integration/storage/dbfs/nvfs_no_regression_spec.spl`
- `bin/simple test test/unit/os/services/vfs/vfs_rootfs_porting_spec.spl`
- `bin/simple test test/unit/os/kernel/loader/elf_loader_spec.spl`
- `bin/simple test test/system/kernel/boot_fs_spec.spl`
- `bin/simple test test/system/kernel/nvfs_elf_load_spec.spl`
- `bin/simple test test/system/kernel/elf_load_chain_spec.spl`
- `bin/simple test test/unit/os/kernel/loader/executable_source_vfs_spec.spl`
- `SIMPLEOS_DBFS_BOOT=1 bin/simple test test/system/os/port/dbfs_disk_boot_spec.spl`
- Known gap: QEMU boot from a native DBFS rootfs and in-guest DBFS executable spawn is not yet covered; current QEMU smoke proves the DBFS-marked FAT32 carrier image build/marker path
