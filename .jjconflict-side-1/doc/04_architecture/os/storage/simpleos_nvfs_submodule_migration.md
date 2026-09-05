<!-- codex-architecture -->
# SimpleOS NVFS Submodule Migration

## Architecture
NVFS is now an OS service package:

- `src/os/services/nvfs/core/` — arena, extent, pmap, checkpoint, scrub, send, compression, dedup, encryption.
- `src/os/services/nvfs/driver/` — native NVFS driver surface.
- `src/os/services/nvfs/posix/` — POSIX-compatible shim.
- `src/os/services/nvfs/tool/` — offline check tool.

The package is exported through `src/os/services/mod.spl`, next to FAT32 and VFS services. DBFS remains under `src/lib/nogc_sync_mut/db/dbfs_*` and continues to share stdlib storage primitives with NVFS.

## Consequences
The old external submodule is no longer a build or import boundary. Cross-submodule workaround comments and imports are replaced with OS-owned `os.services.nvfs` paths.
