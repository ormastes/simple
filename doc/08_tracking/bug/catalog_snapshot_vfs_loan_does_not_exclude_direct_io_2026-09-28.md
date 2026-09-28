# Catalog snapshot admission needs backend write exclusion

**Status:** implementation blocked; no snapshot API added.
**Inspected base:** `e2dab431827448114d0894fb1dd628727f83fa8a` (`origin/main`).
**Scope:** canonical-VFS-loan catalog open/read/hash/seal/close, FAT32/NVFS.

The canonical MountTable loan removes `g_mount_table` and sets an active loan
nonce in `src/os/services/vfs/vfs_boot_state.spl:185`. Ordinary VFS entrypoints
refuse while that loan is active. This is table access exclusion, not evidence
that every backend mutation has completed or is excluded.

`src/os/services/vfs/nvme_filesystem_direct_io.spl:148` accepts a retained
`DriverInstance` and a separate `NvmeFilesystemLease`. For writes it advances
FAT32 content generation before submitting the device request. The batch route
does the same. `src/os/services/vfs/nvme_boot_runtime_owner.spl:414` and its
batch counterparts validate the independent storage lease and submit through
the adapter without consulting the MountTable loan.

The FAT32 hook in `src/lib/nogc_async_mut/fs_driver/fat32_file_ops.spl:110`
records neither a write-in-progress state nor a completion transition. An
interleaving can therefore be:

1. A direct writer increments generation and has not yet completed its write.
2. A snapshot acquires the VFS table loan and records that incremented value.
3. The snapshot reads some old bytes; the independent write changes storage.
4. Later snapshot reads see changed bytes, while its final generation matches.

An owner-held SHA256 would authenticate the observed stream, but would not
establish that the stream was one stable file version. Holding a snapshot
registry mutex does not exclude the independent write route.

## Required prerequisite

Bind snapshot admission to an owner-issued backend read/exclusion lease which
drains prior writes and prevents new writes, or provide a shared mutation
protocol whose in-progress state is visible before any write and whose
completion/failure transitions cannot be missed by a snapshot. Every admitted
buffered/direct mutation must participate. Do not substitute a MountTable-local
counter or a caller assertion that boot is quiet. A narrower immutable/read-only
media admission is possible only if the storage owner actually enforces it.

The inspected base also lacks `DbFsDriver.file_generation_v1`, called by
`src/lib/nogc_sync_mut/fs_driver/nvfs_driver.spl:140`. The separately developed
DBFS retained-inode generation change must be integrated before NVFS can form
a complete source closure. PR #1877 supplies that query but remains draft and
unmerged; it is not evidence that this base already provides it.

FAT32 class sharing is not the blocker: copied `FsFat32Driver` values share
their `Fat32Core` class, including its generation table. The remaining gap is
mutation exclusion and observation ordering.

## Evidence limit

This report is source analysis, not a reproduced concurrent device execution.
No runtime checks were attempted: there is no admitted source-matched
pure-Simple runtime for this slice. No snapshot implementation, execution
claim, guest argv qualification, or release qualification is made.
