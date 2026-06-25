# Design — storage_fat32_handle_metadata

The FsDriver interface now includes `opendir(path) -> Result<DirHandle, FsError>` so
directory handles are created by drivers instead of guessed by callers.

Fat32 wrapper behavior:
- `open` already stores `FileHandle -> path`; `fstat` delegates through `stat(path)`.
- `opendir` validates the path by calling the underlying path-based FAT32 `readdir`,
  then stores `DirHandle -> path`.
- `readdir(DirHandle)` resolves the stored path, calls FAT32 `readdir(path)`, and maps
  core directory entries into `std.fs_driver.types.DirEntry`.

Other drivers:
- RamFs, Nvfs, and NvfsPosix use the resolved directory inode id as the `DirHandle.id`.
