# System Test Plan — storage_fat32_handle_metadata

Spec: `test/system/storage_fat32_handle_metadata_spec.spl`

Coverage:
- Through the shared FsDriver surface, open a file, compare `fstat(handle)` with
  `stat(path)`, and verify size.
- Create a directory, open it with `opendir`, then pass the returned handle to `readdir`.
- FAT32-specific wrapper code is covered by source checks because the interpreter binds
  `std.fs_driver.fat32_stub` to a cached wrapper/core class name collision in runtime tests.

Acceptance mapping:
- FR-STORAGE-0003 AC1: `fstat(FileHandle)` matches path stat.
- AC2/AC3: `opendir(path)` exists and returns a handle accepted by `readdir`.
- AC4: focused source checks and existing fs-driver tests run after implementation.
