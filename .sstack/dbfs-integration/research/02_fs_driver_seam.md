# Stream B — FsDriver / MountTable Seam

**Date:** 2026-04-28

## FsDriver Trait Surface

**File:** `src/lib/nogc_sync_mut/fs_driver/ops.spl`

Full trait (all signatures present, no bodies):
- Lifecycle: `mount(opts)`, `unmount()`, `remount(opts)`, `statfs()`
- Root: `root() -> Inode`
- File I/O: `open(path, flags) -> FileHandle`, `close(handle)`, `read(handle, offset, buf)`, `write(handle, offset, buf)`, `pread`, `pwrite`, `fstat(handle)`, `stat(path)`, `opendir(path)`, `truncate(path, length)`
- Namespace: `readdir(DirHandle) -> DirEntry`, `mkdir`, `rmdir`, `unlink`, `rename`, `symlink`, `readlink`, `link`
- Extension probe: `capabilities() -> CapabilitySet`, `probe(cap: Capability) -> Option<Extension>`

## DriverInstance Enum — Current Variants

**File:** `src/lib/nogc_sync_mut/fs_driver/instance.spl`

```
enum DriverInstance:
    Fat32(driver: FsFat32Driver)
    Nvfs(driver: NvfsDriver)
    NvfsPosix(driver: NvfsPosixDriver)
    RamFs(driver: RamFsDriver)
```

`impl DriverInstance` has one method: `driver_name() -> text` — exhaustive match over all 4 variants.

## Exhaustive Match Sites

Files that contain `DriverInstance` or dispatch on variants — ALL must be updated when `DbFs` variant is added:

| File | Reason for update |
|---|---|
| `src/lib/nogc_sync_mut/fs_driver/instance.spl` | Add `DbFs(driver: DbFsDriver)` variant + arm in `driver_name()` |
| `src/lib/nogc_sync_mut/fs_driver/mount_table.spl` | `MountEntry.driver: DriverInstance`; any match arms on driver type |
| `src/lib/nogc_sync_mut/fs_driver/ops.spl` | Referenced in dispatch examples in docstring |
| `src/lib/nogc_sync_mut/fs_driver/__init__.spl` | Module re-export — may need to export `DbFsDriver` |
| `src/lib/nogc_sync_mut/driver/core.spl` | References DriverInstance — check for match arms |
| `src/os/services/vfs/vfs_init.spl` | Uses `DriverInstance` for mounting; add DBFS mount path |

**Note:** The compiler enforces exhaustive match — adding the variant will produce compile errors at every unhandled match site, which is the intended discovery mechanism.

## FsExtension Capability Enum

**File:** `src/lib/nogc_sync_mut/fs_driver/capability.spl`

23 variants defined:
`COW, Snapshot, Clone, Dedup, Checksum, SelfHeal, SendReceive, Compress, Encrypt, Quota, Reflink, Atime, Xattr, Acl, CaseFold, Hardlinks, SparseFiles, LargeFiles, UnicodeNames, CaseSensitive, PosixCompat, AsyncIo, DirectIo`

**DBFS should declare support for (per AC-8):** `COW`, `Snapshot` (stretch), `Xattr`, `Acl`, `LargeFiles`, `PosixCompat`, `Reflink` (stretch). No new Capability variants needed.

## Extension Enum

**File:** `src/lib/nogc_sync_mut/fs_driver/extension.spl`

Extension enum has 11 variants: `Snapshot, Dedup, Checksum, SendReceive, Scrub, Compress, Encrypt, Quota, Reflink, PosixCompat, DirectIo`. All are stub structs currently ("agents B/C/D fill in").

**DBFS required:** Implement `PosixCompatExt` (random write COW shadow, rename-over, unlink-while-open, truncate). Others are stretch.

## Exact Edit — `DbFs` Variant Addition

**File to edit:** `src/lib/nogc_sync_mut/fs_driver/instance.spl`

Add to `enum DriverInstance`:
```
    DbFs(driver: DbFsDriver)
```

Add arm to `impl DriverInstance.driver_name()`:
```
    case DbFs(d): d.name
```

**New file needed:** `src/lib/nogc_sync_mut/fs_driver/dbfs_stub.spl` (analogous to `fat32_stub.spl` and `ramfs.spl`) — a `DbFsDriver` struct implementing the `FsDriver` trait.

## Mount Table Integration

`MountTable.mount(path, driver, opts)` accepts any `DriverInstance`. No changes to `MountTable` itself. VFS init (`vfs_init.spl`) needs a new code path:
```
MountTable.mount("/data", DriverInstance.DbFs(DbFsDriver.new(block_dev)), opts)
```
