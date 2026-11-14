# VfsHandleTable rewound to unbounded u64 `register` while vfs.spl kept the Result caller

- **Status:** fixed (2026-11-15)
- **Reproducer:** `test/01_unit/os/services/vfs/container_lookup_enforcement_spec.spl`
  (`method is_err not found on type u64` at `vfs.spl:291`). Companion:
  `test/01_unit/os/kernel/fs/handle_mount_association_spec.spl`.

## Root cause
`4b88aebf00b` made `VfsHandleTable.register` bounded (`VFS_HANDLE_TABLE_MAX_OPEN`,
generation cap) and return `Result<u64, text>`. `VfsManager.open` was updated to roll
back the driver handle when admission is refused. The release transplant `88aac2ffe28`
then rewound `src/os/kernel/fs/vfs_handle_table.spl` and its spec to the pre-4b88
versions but kept the new `vfs.spl`. That is a stale-snapshot rewind.

## Fix
Restored both files from `4b88aebf00b`. Separately, the spec's `YesFs` mock now
implements the trait methods `stat_no_follow` and `readlink`, which the Filesystem
trait gained.

## Verification
- container_lookup_enforcement_spec: OK 13/13
- handle_mount_association_spec: OK 11/11
