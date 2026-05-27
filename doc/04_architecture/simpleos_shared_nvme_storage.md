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
- `src/lib/nogc_sync_mut/fs_driver/nvfs_driver.spl` now has a device-backed
  constructor so FAT32, NVFS, and DBFS all expose a shared `BlockDevice`
  construction path.
- `src/os/services/vfs/nvme_filesystem_mounts.spl` converts a validated
  `NvmeFilesystemLease` plus a lease-backed `BlockDevice` into the
  `DriverInstance` needed by the VFS mount table.
- `src/os/services/vfs/vfs_boot_init.spl` builds the pure-Simple boot FAT32
  adapter through the same `NvmeFilesystemLease` contract instead of a
  whole-device `NvmeBlockAdapter`, and the VFS boot initializer tries that path
  before the C bridge fallback.
- `src/os/kernel/ipc/dma_alloc_contract.spl` documents the syscall 84 layout:
  the syscall return is the CPU virtual address, result word 0 is the
  device-visible physical address, and result word 1 remains the allocation id.
- `src/os/kernel/types/device_mem_types.spl`, `src/os/services/pcimgr/pcimgr.spl`,
  and `src/os/kernel/ipc/syscall_device.spl` issue tokenized BAR/IRQ/DMA/IOMMU
  grant metadata for user-space direct driver handoff.

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
- FAT32, NVFS, and DBFS can each mount from the same lease-backed
  `BlockDevice` interface instead of filesystem-specific NVMe code.
- VFS code has one mount-factory entry point for selecting FAT32, NVFS, or DBFS
  from the same lease validation path.
- Pure Simple NVMe DMA allocation now uses the same syscall contract as
  user-space DMA descriptors, so result word 1 is no longer mistaken for a
  virtual address.
- User-assigned namespace leases can consume a `DeviceGrant` resource-set label
  instead of a hand-written token string.
- The pure-Simple boot FAT32 helper is now lease-bounded before FAT32 sees the
  device, which keeps system boot storage on the same contract as NVFS and DBFS.
- VFS boot now prefers the pure-Simple NVMe/FAT32 path; the C bridge is fallback
  behavior rather than the first storage path.
- A successful pure-Simple FAT32 boot loads the app manifest and executable
  cache from the lease-backed FAT32 root; pure boot validation does not fall
  through to C-backed reads.
- VFS exposes boot storage provider state and a production acceptance helper so
  `VFS ready` is not treated as production-ready NVMe unless it came from the
  pure-Simple `simple-driver` path.
- Production VFS boot has a fail-closed entry point: development boots may keep
  the C bridge fallback, but production NVMe boot rejects fallback-backed VFS
  readiness.
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
- The top-level baremetal boot entry still keeps the C NVMe/FAT32 bridge as a
  fallback until the pure-Simple FAT32 mount path has hardware-safe behavior on
  every boot image variant.

## Verification
- `test/unit/os/drivers/nvme/nvme_storage_model_spec.spl` covers system leases,
  user-assigned leases, grant failures, reserved queue rejection, and shared
  FAT32/NVFS/DBFS block-interface readiness.
- `test/unit/os/services/vfs/nvme_block_adapter_spec.spl` covers adapter-visible
  lease translation and out-of-range rejection without requiring real hardware.
- `test/unit/lib/fs_driver/nvfs_device_backed_spec.spl` covers NVFS opening on
  the same shared `BlockDevice` surface used by FAT32 and DBFS.
- `test/unit/os/services/vfs/nvme_filesystem_mounts_spec.spl` covers producing
  FAT32, NVFS, and DBFS `DriverInstance` values from one NVMe lease contract.
- `test/unit/os/kernel/ipc/dma_alloc_contract_spec.spl` covers the DMA syscall
  result layout used by the pure Simple NVMe driver and VFS adapter.
- `test/unit/os/kernel/types/device_mem_types_spec.spl` covers DeviceGrant
  BAR/IRQ/DMA/IOMMU token metadata, and the NVMe storage model spec covers using
  that label for a user-assigned namespace lease.
- `test/unit/os/services/vfs/vfs_boot_nvme_lease_spec.spl` covers the
  pure-Simple boot FAT32 lease helper and rejects invalid namespace geometry
  before mounting.
