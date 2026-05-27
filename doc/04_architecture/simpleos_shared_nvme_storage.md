<!-- codex-architecture -->
# SimpleOS Shared NVMe Storage

## Status
Proposed

## Context
SimpleOS needs one production NVMe hardware driver path that can serve both
system filesystems and user-space driver assignments. FAT32, NVFS, and DBFS
must not each grow separate NVMe access paths. The existing code already has:

- `src/os/drivers/nvme/nvme_storage_model.spl` for namespace and queue policy.
- `src/os/drivers/nvme/block_device.spl` for physical DMA block traits.
- `src/lib/nogc_sync_mut/fs_driver/block_device.spl` for filesystem-facing
  byte-buffer sector I/O.
- `src/lib/nogc_sync_mut/db/dbfs_engine/raw_nvme_arena.spl` and
  `src/lib/nogc_sync_mut/db/dbfs_driver/dbfs_driver.spl` for DBFS device-backed
  arenas.
- `src/lib/nogc_sync_mut/fs_driver/fat32_core.spl` and NVFS arena/superblock
  modules already written against shared `BlockDevice` concepts.

## Decision
The NVMe driver owns controller init, namespace discovery, queue assignment,
doorbells, DMA, and IRQ/completion handling. Filesystems receive an
`NvmeFilesystemLease`: a bounded namespace slice with queue policy and
provider/grant metadata. The lease is accepted only when:

- Provider is pure Simple (`simple-driver`).
- FAT32/NVFS/DBFS consume the shared filesystem block interface.
- The LBA window is inside the identified namespace.
- System namespaces use the reserved system queue.
- User-assigned namespaces use data queues, issued resource-grant tokens,
  non-secure resource namespace mode, and an IOMMU/grant-broker boundary.

This keeps common parsing/state-machine/queue policy in shared Simple code,
while direct MMIO/DMA/IRQ/doorbell access remains gated for user-space drivers.

## Consequences
### Positive
- FAT32, NVFS, and DBFS can share one NVMe namespace lease contract.
- User-space namespace assignment is explicit and testable.
- System boot/root storage and user-assigned storage are separated by queue role.
- The contract is compatible with the existing DBFS `RawNvmeArena` and FAT/NVFS
  `BlockDevice` surfaces.

### Negative
- This is still a contract/model layer; it does not by itself prove real hardware
  DMA completion or production queue depth performance.
- FAT32/NVFS/DBFS mounting still needs end-to-end hardware verification on real
  namespaces, but the VFS NVMe adapter now enforces the lease window before
  translating filesystem-relative LBAs to physical namespace LBAs.

## Verification
- `test/unit/os/drivers/nvme/nvme_storage_model_spec.spl` covers system leases,
  user-assigned leases, grant failures, reserved queue rejection, and shared
  FAT32/NVFS/DBFS block-interface readiness.
- `test/unit/os/services/vfs/nvme_block_adapter_spec.spl` covers adapter-visible
  lease translation and out-of-range rejection without requiring real hardware.
