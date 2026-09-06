# Local Research — storage_fat32_handle_metadata

Feature request: `FR-STORAGE-0003`.

Findings:
- `src/lib/nogc_sync_mut/fs_driver/fat32_stub.spl` already keeps `path` in
  `Fat32HandleEntry`, so `fstat(FileHandle)` can delegate to `stat(path)`.
- The wrapper also has `Fat32DirHandleEntry`, but `FsDriver` did not expose `opendir`,
  leaving no supported way to create a `DirHandle`.
- Existing NVFS drivers use `DirHandle.id` as a namespace inode id. RamFs can do the
  same by resolving a directory path to an inode id.

Implementation scope:
- Add `opendir(path)` to `FsDriver`.
- Implement `opendir` for Fat32, RamFs, Nvfs, and NvfsPosix.
- Implement Fat32 `fstat` and `readdir` via the existing path-backed handle tables.
