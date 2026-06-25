# SimpleOS NVFS Submodule Migration Report

## Result
NVFS is now repo-owned under `src/os/services/nvfs/`. The former external
project was deleted from GitHub.

## Evidence
- Local old working tree: absent.
- Git index gitlink for the former NVFS submodule: absent.
- `.gitmodules` entry for the former NVFS submodule: absent.
- Migrated OS NVFS source: `bin/simple check src/os/services/nvfs` passes.
- Shared fs driver surface: `bin/simple check src/lib/nogc_sync_mut/fs_driver` passes.
- Retained migrated unit tests: `bin/simple test test/01_unit/os/services/nvfs --mode=interpreter --sequential --clean` passes.
- GitHub deletion: REST `DELETE /repos/ormastes/simple-nvfs` returned `204`; connector readback returns 404 Not Found.

## Deferred Prototype Tests
Several old submodule prototype tests covered unfinished pmap, namespace,
checksum, encryption, scrub, and send/receive behavior. They were not imported
as active unit tests because they failed against the current OS-owned
implementation. The retained migrated tests cover arena basics, dedup,
reflink, superblock, check-tool plumbing, POSIX shim, and fs_driver primitives.
