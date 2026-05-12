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
- ELF binary load from NVFS/DBFS arena
- Shared BTree<V>, checkpoint_ring, intent_log in storage/shared/
- NVFS fd_table (NvfsFdEntry) wired into NvfsPosixDriver

## TODO

- Shared WAL extraction (`dbfs_engine/wal.spl` → `storage/shared/wal.spl`)
- Recovery side effects (wire arena_discard + checkpoint write in recovery.spl)
- Intent log Arena-backed persistence (beyond sector-level)
- Checkpoint ring Arena-backed persistence (beyond sector-level)
- Pager extraction (low priority, only DBFS uses it)
- Samsung NVMe features: FDP, ZNS (deferred)
- QEMU end-to-end boot + mount + file I/O test
