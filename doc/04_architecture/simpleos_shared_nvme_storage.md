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
- The fail-closed production boot entry is exported through the VFS public
  surface so production boot code can select it instead of the development
  fallback initializer.
- Kernel boot service initialization and the FAT32 root fallback in
  `boot_fs.spl` now select the production VFS boot gate, so those production
  paths no longer treat C-backed VFS readiness as acceptable storage.
- The freestanding `os_main` root probe now calls a production wrapper that
  rejects the C-only boot bridge result instead of marking it mounted.
- Freestanding NVFS/DBFS superblock probing is split into provider-independent
  `BlockDevice` helpers, leaving a concrete insertion point for a freestanding
  pure-Simple NVMe adapter without duplicating filesystem probe logic.
- Freestanding root probing now has one provider-neutral `BlockDevice` entry
  point that tries NVFS then DBFS, so a pure-Simple NVMe adapter does not need
  filesystem-specific boot wiring.
- Real-device readiness now treats `c-boot-bridge` as non-production evidence;
  only the pure-Simple `simple-driver` provider can satisfy storage readiness.
- `src/os/kernel/boot/freestanding_nvme_adapter_contract.spl` defines the
  evidence gate for a freestanding pure-Simple NVMe adapter before it may enter
  the shared `boot_fs_mount_from_device` filesystem probe.
- `boot_fs_mount_pure_nvme_from_device` connects that evidence gate to the
  freestanding filesystem probe, so a future pure-Simple adapter must prove
  transfer readiness before NVFS/DBFS probing starts.
- NVMe read/write/flush command construction now lives in a syscall-free shared
  transfer module. Hosted and freestanding drivers can use the same LBA bounds,
  NLB encoding, DMA pointer validation, and completion-status decoding instead
  of duplicating C-bridge or syscall-specific logic.
- `NvmeQueuePair` submission and polling are now syscall-free. Hosted
  notification waiting lives in a separate companion module, so freestanding
  system-driver boot code can reuse SQ/CQ ring mechanics without importing the
  user/hosted `NotificationWait` path.
- Freestanding queue construction has a syscall-free resource builder that
  validates platform-owned BAR0, DMA queue memory, queue depth, DMA alignment,
  and doorbell stride before constructing the shared `NvmeQueuePair`.
- Hosted NVMe initialization now uses the same queue resource builder for
  completed admin and I/O queue pairs, so user-space and freestanding/system
  paths share doorbell stride conversion, resource validation, and queue-pair
  construction instead of carrying separate doorbell math.
- NVMe admin command construction for identify, set-features queue count, and
  I/O queue creation now lives in a syscall-free shared module. Hosted,
  user-space, and freestanding/system driver paths can submit the same encoded
  controller setup commands after their own BAR/DMA ownership is established.
- Namespace identify parsing now uses the shared controller contract and refuses
  invalid namespace geometry instead of silently falling back to 512-byte
  sectors. FAT32, NVFS, and DBFS leases must be backed by the same proven
  namespace LBA count and formatted LBA size.
- Hosted controller initialization now validates CAP/VS/CSTS through the shared
  controller facts contract before queue setup and uses the shared controller
  enable CC value. User-space and freestanding/system paths therefore share the
  same controller capability and enable policy.
- The baremetal initializer no longer has a permissive fallback lane. It uses
  the shared controller validation, DMA allocation wrapper, queue resource
  builder, admin command builders, namespace parser, and I/O queue setup, and it
  fails closed when identify or queue creation fails.
- Reversible sector probing is now represented as a structured contract with
  LBA, byte length, completion status, read/write/restore results, and a flag
  proving the probe used the shared transfer command logic. Freestanding
  readiness consumes that contract instead of loose booleans.
- The hosted NVMe driver can now produce that structured evidence by executing
  a real polling read/write/verify/restore sector probe through its shared
  `read_sectors`/`write_sectors` transfer path.
- The hosted NVMe driver can also convert the executable probe result into the
  standard `NvmeTransferEvidence` consumed by boot and VFS gates, using explicit
  placement, grant, namespace, DMA-isolation, and IOMMU/broker metadata supplied
  by the caller.
- `NvmeTransferEvidence` is now the production precondition for minting a
  filesystem lease: the storage model refuses FAT32/NVFS/DBFS leases when the
  pure-Simple driver has not proved queue readiness, completion, reversible
  sector I/O, shared logic, and the correct system/user namespace ownership.
- The VFS boot layer has an evidence-gated FAT32 lease constructor for
  production boot; the older geometry-only lease helper remains a compatibility
  path until real boot supplies hardware evidence directly.
- The pure-Simple NVMe/FAT32 boot path now executes the driver's reversible
  sector probe, converts it into system-driver transfer evidence, and mints the
  boot FAT32 lease through the evidence-gated constructor before creating the
  VFS block adapter.
- Freestanding controller readiness now has an explicit resource contract that
  binds system-driver or user-space-driver placement, grant/namespace mode,
  admin queue resources, I/O queue resources, DMA isolation, and IOMMU/broker
  state before producing transfer evidence.
- System-driver NVMe transfer evidence uses kernel-owned system namespace
  resources; user-space driver evidence still requires issued grant tokens and
  non-secure user-assigned resource namespaces.
- User-space namespace assignment has a concrete helper that takes the issued
  `DeviceGrant`, validates resource tokens and IOMMU isolation, verifies that
  transfer evidence belongs to that grant, assigns a data queue, and emits the
  same FAT32/NVFS/DBFS lease surface as system boot storage. The checked helper
  also evaluates active namespace leases before exposing the user assignment.
- System boot/root storage and user-assigned storage are separated by queue role.
- Namespace lease admission now has a shared conflict check: the same
  controller namespace cannot be system-owned and user-assigned at the same
  time, and repeated user filesystem views are accepted only for the same grant,
  owner task, and queue.
- The VFS NVMe mount factory exposes a checked mount entry point that applies
  that active-lease conflict rule before constructing FAT32, NVFS, or DBFS
  driver instances.
- Pure-Simple VFS boot records its system FAT32 NVMe lease as an active lease,
  so later user-space namespace assignment can be checked against the boot-owned
  namespace before it is mounted. VFS also exposes a user-assignment entry point
  that records the user lease after successful active-lease admission, plus a
  driver-instance entry point that records only after FAT32/NVFS/DBFS driver
  construction succeeds. Active user leases can be released by the exact
  namespace/mode/grant/owner/queue assignment so unmount can make the namespace
  assignable again.
- The contract is compatible with the existing DBFS `RawNvmeArena` and FAT/NVFS
  `BlockDevice` surfaces.
- Production performance claims now have an explicit NVMe contract: measured
  samples must be warm 4K random read/write runs on the pure Simple provider,
  without the C bridge or per-I/O allocation, with enough queue depth and common
  logic sharing, and Simple must beat the C FAT baseline for read/write IOPS and
  p99 latency.
- Hardware runners can emit one `nvme_perf` line from measured counters through
  the performance report helper; serial acceptance re-parses the numeric fields
  and rejects missing fields, invalid values, insufficient warm/queue settings,
  and Simple-not-faster-than-C counters before release gates can treat the run
  as production evidence.
- The q35 pure-Simple real-device marker contract now lists `nvme_perf
  reason=ready`, and serial acceptance validates the detailed performance fields
  in addition to provider, grant, namespace, and transfer markers.

### Negative
- This is still a contract/model layer; it does not by itself prove real hardware
  DMA completion or production queue depth performance.
- FAT32/NVFS/DBFS mounting still needs end-to-end hardware verification on real
  namespaces, but the VFS NVMe adapter now enforces the lease window before
  translating filesystem-relative LBAs to physical namespace LBAs.
- The top-level baremetal boot entry still keeps the C NVMe/FAT32 bridge as a
  fallback until the pure-Simple FAT32 mount path has hardware-safe behavior on
  every boot image variant.
- The freestanding adapter still needs queue memory ownership and MMIO BAR
  mapping from the boot allocator/platform path; the shared transfer module only
  removes duplicated command construction and range validation.
- Freestanding queue use still needs platform-owned timeout and interrupt policy
  once it has real MMIO/DMA ownership; the reusable queue module currently
  provides polling mechanics only.
- The queue resource builder does not allocate memory or map BARs; those remain
  responsibilities of the system boot allocator or user-space grant broker.
- Controller resource readiness still does not claim production transfer by
  itself. The evidence path remains fail-closed until real hardware completion
  plus read/write/restore sector probes are supplied.
- Invalid namespace identify data is a hard driver error for production paths;
  it is not converted into a fake default sector size.
- Invalid controller facts are a hard error before admin queues are allocated,
  so unsupported controllers cannot appear as partially initialized storage.
- Baremetal initialization no longer reports initialized storage after failed
  identify or failed I/O queue creation.
- Sector probe evidence is not sufficient unless it records successful
  completion, read, write, restore, and shared transfer logic usage.
- Probe I/O failures return non-ready structured evidence rather than marking
  storage ready; invalid probe preconditions still return driver errors.
- Transfer evidence production remains fail-closed: probe precondition failures
  return errors, while probe I/O failures become evidence that the boot/VFS gates
  reject.
- Queue assignment is part of filesystem readiness: leases without read, write,
  and queue-submit rights are rejected before FAT32, NVFS, or DBFS can mount.
- Real-hardware performance validation is still required for production
  throughput claims: queue depth, warm 4K random read/write latency, and max RSS
  need measurement on representative NVMe devices.

## Verification
- `test/unit/os/drivers/nvme/nvme_storage_model_spec.spl` covers system leases,
  user-assigned leases, grant failures, reserved queue rejection, required queue
  rights, namespace ownership conflict rejection, evidence-gated lease minting,
  and shared FAT32/NVFS/DBFS block-interface readiness.
- `test/unit/os/drivers/nvme/nvme_namespace_assignment_spec.spl` covers
  user-assigned namespace lease construction from a tokenized `DeviceGrant`,
  grant/evidence mismatch rejection, missing-token rejection, active system/user
  namespace conflict rejection, and FAT32/NVFS/DBFS readiness on the shared
  lease surface.
- `test/unit/os/drivers/nvme/nvme_performance_contract_spec.spl` covers the
  production 4K random read/write measurement contract and rejects C-bridge,
  cold-run, per-I/O allocation, wrong-size, slower-than-C samples, and incomplete
  serial report lines.
- `test/unit/os/drivers/real_device_readiness_spec.spl` covers that pure-Simple
  q35 completion requires the NVMe performance marker and is rejected when the
  evidence line is missing.
- `test/unit/os/services/vfs/nvme_block_adapter_spec.spl` covers adapter-visible
  lease translation and out-of-range rejection without requiring real hardware.
- `test/unit/lib/fs_driver/nvfs_device_backed_spec.spl` covers NVFS opening on
  the same shared `BlockDevice` surface used by FAT32 and DBFS.
- `test/unit/os/services/vfs/nvme_filesystem_mounts_spec.spl` covers producing
  FAT32, NVFS, and DBFS `DriverInstance` values from one NVMe lease contract and
  rejects checked mounts that would mix system/user ownership of one namespace.
- `test/unit/os/services/vfs/vfs_boot_nvme_lease_spec.spl` covers the
  evidence-gated production FAT32 boot lease constructor and guards that the
  pure-Simple boot path calls the hardware probe before mounting, then records
  the boot lease for later system/user conflict admission and records accepted
  user namespace assignments in the same active lease registry after driver
  construction succeeds, including release/reassignment coverage.
- `test/unit/os/kernel/ipc/dma_alloc_contract_spec.spl` covers the DMA syscall
  result layout used by the pure Simple NVMe driver and VFS adapter.
- `test/unit/os/kernel/types/device_mem_types_spec.spl` covers DeviceGrant
  BAR/IRQ/DMA/IOMMU token metadata, and the NVMe storage model spec covers using
  that label for a user-assigned namespace lease.
- `test/unit/os/services/vfs/vfs_boot_nvme_lease_spec.spl` covers the
  pure-Simple boot FAT32 lease helper and rejects invalid namespace geometry
  before mounting.
- `test/unit/os/drivers/nvme/nvme_transfer_command_spec.spl` covers shared
  syscall-free NVMe transfer command construction, zero-count rejection, NLB
  limit rejection, DMA pointer validation, and completion-status decoding.
- `test/unit/os/drivers/nvme/nvme_queue_boundary_spec.spl` guards that the
  reusable queue submission/polling module does not import hosted syscalls or
  notification waits.
- `test/unit/os/drivers/nvme/nvme_queue_resources_spec.spl` covers syscall-free
  construction of `NvmeQueuePair` from owned BAR/DMA resources and rejects
  invalid depth, missing BAR mapping, invalid doorbell stride, unaligned DMA,
  and invalid DSTRD-to-doorbell-stride conversion.
- `test/unit/os/drivers/nvme/nvme_admin_command_spec.spl` covers shared
  syscall-free admin command construction for identify, set queue count, I/O CQ,
  and I/O SQ setup, including rejection of invalid command resources.
- `test/unit/os/drivers/nvme/nvme_freestanding_controller_spec.spl` covers
  freestanding controller resource validation, system-driver evidence, and the
  requirement that real completion and reversible sector probes be supplied
  before transfer readiness becomes `ready`.
- `test/unit/os/drivers/nvme/nvme_sector_probe_spec.spl` covers the structured
  reversible-sector probe contract and rejects missing completion, read, write,
  restore, byte count, or shared transfer logic.
- `test/unit/os/drivers/nvme/nvme_driver_probe_contract_spec.spl` guards that
  the hosted driver probe uses shared read/write sector paths, verifies the
  written pattern, restores the original sector, and returns the structured
  probe result.
