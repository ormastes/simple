<!-- codex-research -->
# SimpleOS NVFS Submodule Migration — Local Research

## Findings
- The old NVFS project was registered as a git submodule at `examples/11_advanced/nvfs` with URL `https://github.com/ormastes/simple-nvfs.git`.
- SimpleOS already has the canonical storage/VFS surface for FAT32, NVFS, and DBFS:
  - `src/os/services/fat32/`
  - `src/os/services/vfs/`
  - `src/lib/nogc_sync_mut/fs_driver/`
  - `src/lib/nogc_sync_mut/db/dbfs_engine/`
- The submodule source contained concrete NVFS core, driver, POSIX shim, and tool code, but also carried old submodule-only import workarounds and placeholder test skips.
- Active architecture docs already require FAT32, NVFS, and DBFS to share one SimpleOS NVMe lease and `BlockDevice` surface.

## Decision
Move the former submodule implementation into `src/os/services/nvfs/`, move usable unit coverage into `test/01_unit/os/services/nvfs/`, remove the submodule registration, and update active references from `examples.nvfs` to `os.services.nvfs`.
