# storage__(src/lib/nogc_sync_mut/fs_driver/fat32_stub.spl_→_fat32.spl)

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-STORAGE-0001"></a>FR-STORAGE-0001 | Fat32Driver: statfs() and truncate/ftruncate not implemented | `Fat32Driver.statfs()` currently returns `pass_todo`. The missing piece is in `src/os/services/fat32/fat32.spl` (class `Fat32Driver`): after `mount()` the geometry fields (`total_clusters`, `sectors_per_cluster`, `bytes_per_sector`) are pop | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
| <a id="feature-FR-STORAGE-0002"></a>FR-STORAGE-0002 | Fat32Driver: true pread/pwrite (cursor-preserving positional I/O) | `FsDriver.pread(handle, offset, buf)` must not advance the file cursor — it is a POSIX `pread(2)` semantics requirement. The current `Fat32Driver` in `src/os/services/fat32/fat32.spl` lacks cursor-save/restore around seek+read. `Fat32OpenFi | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
| <a id="feature-FR-STORAGE-0003"></a>FR-STORAGE-0003 | Fat32Driver: fstat(FileHandle) and readdir(DirHandle) via handle | `FsDriver.fstat(FileHandle)` and `FsDriver.readdir(DirHandle)` both receive opaque handles, not paths. The wrapper in `fat32_stub.spl` maintains a `file_handles: [Fat32HandleEntry]` table with `path: text` per entry, so the information is p | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
