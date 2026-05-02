# NVFS Completion Architecture

Feature set: remaining unchecked NVFS tracker criteria.

## Components

- `src/lib/nogc_sync_mut/fs_driver/mount_table.spl`: path mount resolution via
  indexed char-copy.
- `examples/nvfs/src/core/compression.spl`: class-aware compression using a
  small RLE block frame and raw fallback for incompressible input.
- `examples/nvfs/src/tool/nvfs_upgrade.spl`: record-level offline pmap upgrade
  helper.
- `examples/nvfs/src/core/dedup.spl`: in-memory hot DDT cache, DEDUP tree
  metadata, stats, keyed hashing, and refcount consistency checks.
- `examples/spostgre/test/integration/storage/spostgre_nvfs_e2e_test.spl`:
  MountTable/RamFs integration coverage for WAL bytes.
