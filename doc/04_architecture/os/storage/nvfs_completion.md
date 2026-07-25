# NVFS Completion Architecture

Feature set: remaining unchecked NVFS tracker criteria.

## Components

- `src/lib/nogc_sync_mut/fs_driver/mount_table.spl`: path mount resolution via
  indexed char-copy.
- `src/os/services/nvfs/core/compression.spl`: class-aware compression using a
  small RLE block frame and raw fallback for incompressible input.
- `src/os/services/nvfs/tool/nvfs_upgrade.spl`: record-level offline pmap upgrade
  helper.
- `src/os/services/nvfs/core/dedup.spl`: in-memory hot DDT cache, DEDUP tree
  metadata, stats, keyed hashing, and refcount consistency checks.
- `examples/11_advanced/simple_db/test/02_integration/storage/simple_db_nvfs_e2e_test.spl`:
  MountTable/RamFs integration coverage for WAL bytes.
