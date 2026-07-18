# SimpleOS NVFS Submodule Migration — NFR Requirements

- NFR-NVFS-MIG-001: Do not add executable `pass_todo` placeholders to the migrated OS tree.
- NFR-NVFS-MIG-002: Keep FAT32, NVFS, and DBFS on the shared SimpleOS storage/VFS path.
- NFR-NVFS-MIG-003: Preserve existing unrelated worktree changes.
- NFR-NVFS-MIG-004: Verification must prove `.gitmodules`, the filesystem, and the Git index no longer expose the NVFS submodule.
