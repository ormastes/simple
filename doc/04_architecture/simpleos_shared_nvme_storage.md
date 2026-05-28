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
  construction succeeds. The production hardware entry point builds a
  lease-backed `NvmeBlockAdapter` from the shared `g_nvme` driver and initializes
  its DMA bounce buffer before constructing the filesystem driver. Active user
  leases can be released by the exact
  namespace/mode/grant/owner/queue assignment so unmount can make the namespace
  assignable again.
- The contract is compatible with the existing DBFS `RawNvmeArena` and FAT/NVFS
  `BlockDevice` surfaces.
- The freestanding boot mount path now uses the same provider-neutral
  `BlockDevice` entry point for NVFS, DBFS, and FAT32 probes. FAT32 is detected
  from the sector-0 BPB parser without importing hosted VFS state or the C bridge
  into the pure-Simple adapter entry point.
- Production performance claims now have an explicit NVMe contract: measured
  samples must be warm 4K random read/write runs on the pure Simple provider,
  without the C bridge or per-I/O allocation, with enough queue depth and common
  logic sharing, and Simple must beat a same-device in-guest C NVMe/FAT baseline
  for read/write IOPS and p99 latency. Host page-cache measurements are not
  accepted as q35 production evidence.
- Hardware runners can emit one `nvme_perf` line from measured counters through
  the performance report helper; serial acceptance re-parses the numeric fields
  and rejects missing fields, invalid values, insufficient warm/queue settings,
  and Simple-not-faster-than-C counters before release gates can treat the run
  as production evidence.
- Physical-NVMe production claims must pass the stricter real-hardware serial
  gate as well. That gate layers on top of the `nvme_perf` parser and requires
  `hardware_target=real-nvme`, `qemu=false`, nonempty device model/serial,
  namespace identity, and `measured_on=real-device`; q35/emulator reports are
  rejected even when their counters are faster than the C baseline.
- Real-device runners should emit that line through
  `nvme_real_hardware_perf_report_line_from_measurements`, which appends the
  required physical identity fields to the same measured-counter report and
  normalizes whitespace in model/serial tokens before serial acceptance parses
  them.
- The real-device readiness layer exposes
  `real_device_physical_nvme_serial_acceptance_reason` for physical NVMe logs.
  It requires the pure Simple storage access markers, shared FAT32/NVFS/DBFS
  direct-I/O markers, and the stricter real-hardware performance identity before
  returning `ready`; q35 perf-only output remains insufficient for that gate.
  Physical and q35 perf evidence must now include both
  `storage_placement=user-space-driver` for the assigned namespace and
  `system_storage_placement=system-driver` for the system driver lane.
  Physical NVMe acceptance also requires
  `user_namespace_assignment=hardware-data-queue`,
  `user_namespace_mode=user-assigned`, `user_namespace_queue_id=<data queue>`,
  `user_namespace_direct_io=read-write-through`, and
  `user_namespace_conflict_policy=active-lease-checked`.
  It also requires per-filesystem extent proof:
  `fat32_extent_source=freestanding-fat32-extents`,
  `nvfs_extent_source=freestanding-dbfs-arena`, and
  `dbfs_extent_source=freestanding-dbfs-arena`.
  The performance line must also prove the C comparison baseline with
  `c_baseline_device=same-nvme`, `c_baseline_scope=in-guest`, and
  `c_baseline_cache=direct`.
- Hardware labs can run
  `src/app/simpleos_nvme_serial_check/main.spl --serial-log <path>` against the
  captured serial log. The app delegates to the same physical-NVMe readiness
  gate and exits nonzero when the log is q35/emulator-only or lacks real device
  identity.
- The canonical lab wrapper is `scripts/run_simpleos_physical_nvme_perf.shs`.
  In `--validate-log-only` mode it checks an existing serial capture; otherwise
  it captures from `SERIAL_PORT` for `SIMPLEOS_NVME_SERIAL_SECONDS` and then
  invokes the same checker app.
- The same wrapper supports `--preflight`, which verifies the checker runtime,
  checker app, and at least one host-visible NVMe namespace device before a lab
  run starts. Labs may override the device glob with `SIMPLEOS_NVME_DEVICE_GLOB`.
- Production lab runs should use `SERIAL_PORT=<port> SERIAL_BAUD=<baud>
  scripts/run_simpleos_physical_nvme_perf.shs --production --serial-log <path>
  --serial-seconds=<seconds> --preflight-out <path> --report-out <path>` when
  the host and serial capture are checked in one invocation. The wrapper writes
  the host-visible NVMe identity report first and then requires the captured
  SimpleOS serial identity to match it. Generated production preflight evidence
  is accepted only when the device glob resolves to exactly one namespace, so
  labs must narrow `SIMPLEOS_NVME_DEVICE_GLOB` before assigning a user namespace.
- The q35 pure-Simple real-device marker contract now lists `nvme_perf
  reason=ready`, and serial acceptance validates the detailed performance fields
  in addition to provider, grant, namespace, and transfer markers.
- The standalone q35 pure-NVMe lane now measures its C comparison inside the
  same guest via the C NVMe bridge on the same random LBA sequence after the
  Simple path runs. The `c_bridge_used=false` field still refers to the Simple
  data path; the C bridge is only the measured comparison baseline.
- The q35 pure-NVMe lane also records which filesystem extent source fed the
  Simple direct-I/O offsets. FAT32 uses a freestanding FAT fixture extent path
  over `/SYS/PERF/FAT4K.BIN`; NVFS and DBFS use their shared DBFS arena DirectIo
  formula. The catalog requires
  `fat32_extent_source=freestanding-fat32-extents`,
  `nvfs_extent_source=freestanding-dbfs-arena`, and
  `dbfs_extent_source=freestanding-dbfs-arena` before treating the lane as proof
  that the shared NVMe interface is suitable for all three filesystems.
- VFS tracks direct-I/O adapter ownership by the exact NVMe filesystem lease
  instead of by active-lease array position. Lease-only user namespace
  admission, system boot leases, and hardware-backed FAT32/NVFS/DBFS adapters
  can coexist without releasing one lease shifting another lease onto the wrong
  direct adapter.
- Batched direct-I/O validation now lives in the shared stdlib DirectIo module
  used by hosted and SimpleOS storage code. The NVMe adapter still owns the
  hardware submission, but handle/op/timeout/alignment/buffer-size checks and
  submitted-byte reporting are common logic rather than adapter-local policy.
- Active user namespace leases are treated as exact lease identities for
  release and direct-adapter routing, including base LBA, length, namespace
  geometry, and queue depth. Reusing the same owner/grant/queue for a different
  namespace window is rejected instead of becoming an ambiguous alias.
- Freestanding pure-NVMe root probing now has a lease-admitted entry point:
  transfer evidence must be ready and one NVMe filesystem lease must be ready
  for FAT32, NVFS, and DBFS before the provider-neutral root probe may read
  sectors from the device.
- User data queue reuse is now bound to controller id, namespace id, owner task,
  and queue depth. A hardware user namespace assignment cannot reuse an existing
  queue id for a different namespace or owner.
- The hosted `boot_fs_sequence()` default is production-safe: it no longer
  probes NVFS/DBFS through the C bridge. The C-backed hosted root probing path is
  retained only behind an explicitly named development helper.
- The filesystem-facing NVMe `BlockDevice` sector path now has behavioral
  coverage for the same lease-window translation used at runtime: sector access
  maps through `base_lba` and rejects the first LBA beyond `lba_count`.
- Production VFS root mounting now has a checked NVMe lease entry point that
  constructs FAT32/NVFS/DBFS from `NvmeFilesystemLease` plus `BlockDevice`
  before mounting `/`; the arbitrary-driver root mount helper remains a
  low-level compatibility path for tests and explicitly constructed drivers.

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
- Hardware-backed user namespace mounts are gated on the already-mounted
  pure-Simple boot storage and the initialized shared `NvmeDriver` before VFS
  constructs a lease-backed `NvmeBlockAdapter`; no user/system assignment can
  touch the global controller driver while boot storage is unmounted, C-backed,
  VirtIO-backed, uninitialized, or reporting invalid namespace geometry.
- Failed hardware-backed user namespace admission restores the previously
  identified system namespace after queue-creation or adapter-validation
  failures, so a rejected user assignment cannot leave the shared system driver
  pointed at the user namespace.
- User-assigned namespace leases require the queue owner to match the task
  encoded in the issued `DeviceGrant` BAR/IRQ/DMA/IOMMU tokens, so a grant
  issued to one user-space driver cannot be reused to expose FAT32, NVFS, or
  DBFS over another task's data queue.
- The hardware `NvmeBlockAdapter` rejects leases whose NSID does not match the
  namespace currently identified by `NvmeDriver` before issuing read/write
  commands. This keeps multi-namespace user assignments fail-closed until the
  driver can identify and submit I/O to each assigned namespace explicitly.
- NVMe transfer command construction and `NvmeDriver` now expose namespace-aware
  read/write entry points. Existing namespace-1 I/O delegates through those
  entry points, while non-identified namespaces still fail closed; this gives
  the user/system namespace assignment path the correct hardware API shape
  before enabling true multi-namespace submission.
- `NvmeDriver` stores the NSID returned by namespace identify and uses that
  state for read, write, and flush command submission. The default boot path
  still identifies NSID 1, but the driver now has an explicit
  `identify_namespace_id(nsid)` entry point needed for future user-assigned
  namespaces.
- The VFS hardware user-assignment path now identifies the lease namespace
  before constructing a hardware `NvmeBlockAdapter`, and the adapter stores the
  lease NSID and uses namespace-aware driver read/write methods for FAT32, NVFS,
  and DBFS block I/O.
- The NVMe driver keeps identified namespace geometry per NSID, so a
  lease-backed adapter can validate and submit I/O for its assigned namespace
  without depending on a single mutable current-namespace check.
- The lease-backed adapter rejects stale lease geometry when the identified
  namespace sector count or sector size differs from the lease, and the VFS
  user-assignment path restores the previous identified NSID after recording the
  user namespace facts so legacy boot-namespace operations are not redirected.
- Hardware user namespace assignment now requires the driver to create or reuse
  the lease's user data I/O queue before mounting. Controller initialization
  requests enough I/O queues for the system queue and the bounded data-queue
  range before queue creation; lease-backed FAT32/NVFS/DBFS adapters store that
  queue ID and submit namespace I/O through queue-aware driver methods instead
  of always using the system I/O queue.
- The q35 pure-NVMe lane now proves that hardware path directly: it creates the
  first user data queue, mints a user-assigned lease from the grant, and performs
  4KiB read/write through that queue before emitting
  `user_namespace_assignment=hardware-data-queue`.
- The shared DMA fast path is now namespace- and queue-aware as well: user-space
  storage services can submit preallocated DMA buffers on the assigned namespace
  queue, while the legacy shared-DMA methods delegate to the current system
  namespace queue. This is the no-per-I/O-allocation path production 4K random
  I/O benchmarks must exercise.
- Flush is namespace- and queue-aware too. FAT32, NVFS, and DBFS direct-write
  paths call the lease-backed adapter's explicit flush hook for the same
  assigned namespace queue used for read/write, instead of flushing only the
  current system namespace. The adapter also exposes write-through DirectIo
  submission helpers that pair a direct write or write batch with that same
  lease-queue flush and report `submitted-flushed` on durable completion.
- The lease-backed VFS NVMe adapter exposes explicit 4KiB shared-DMA read/write
  entry points over the same lease NSID and queue ID used by FAT32, NVFS, and
  DBFS. The common filesystem mount surface stays `BlockDevice`, while
  production random-I/O runners and future filesystem direct-I/O hooks can bypass
  byte-array bounce copies with caller-owned DMA buffers.
- The filesystem DirectIo contract now includes a bounded batch request shape,
  and the lease-backed NVMe adapter routes those batches to the same
  namespace/queue-aware shared-DMA 4KiB batch driver path used by q35
  performance evidence. This makes the no-per-I/O-allocation path available
  through the shared FAT32/NVFS/DBFS storage surface instead of only a benchmark
  helper.
- The 4KiB shared-DMA driver path now encodes each 4KiB slot as one NVMe
  multi-sector command when the namespace LBA size is smaller than 4KiB. The
  batch path therefore spends queue entries on filesystem 4KiB operations, not
  on internal 512-byte sectors.
- The q35 performance probes exercise batched 4KiB random I/O over that shared
  lease path, so the evidence lanes measure the production filesystem-facing
  adapter rather than a sector-by-sector benchmark shortcut. The full VFS probe
  advertises the queue-depth-sized 32-operation batch path; the standalone q35
  lane uses a smaller measured batch window when that is faster on QEMU. The
  standalone q35 lane also submits through `NvmeBlockAdapter` DirectIo requests,
  and its write probes use the write-through lease helpers, so the
  filesystem-facing adapter surface is measured against the in-guest C baseline
  instead of a raw `NvmeDriver` shortcut. The `fs_consumers` marker is
  emitted only after the measured loop has routed DirectIo batches for FAT32,
  NVFS, and DBFS through that shared adapter surface. The full VFS boot perf
  helper also derives the same marker from lease readiness for FAT32, NVFS, and
  DBFS instead of printing a static consumer list.
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
  grant/evidence mismatch rejection, grant owner mismatch rejection,
  missing-token rejection, active system/user namespace conflict rejection, and
  FAT32/NVFS/DBFS readiness on the shared lease surface.
- `test/unit/os/drivers/nvme/nvme_performance_contract_spec.spl` covers the
  production 4K random read/write measurement contract and rejects C-bridge,
  cold-run, per-I/O allocation, wrong-size, slower-than-C samples, and incomplete
  serial report lines.
- `test/unit/os/drivers/real_device_readiness_spec.spl` covers that pure-Simple
  q35 completion requires the NVMe performance marker and is rejected when the
  evidence line is missing.
- `test/unit/os/services/vfs/nvme_block_adapter_spec.spl` covers adapter-visible
  lease translation, out-of-range rejection, and fail-closed rejection when a
  lease NSID is not the driver's identified namespace, and guards that
  lease-backed I/O calls namespace-aware single and batched direct-I/O driver
  methods without requiring real hardware.
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
  construction succeeds, including hardware-adapter routing, fail-closed shared
  driver readiness gating, and release/reassignment coverage.
- `test/unit/os/kernel/ipc/dma_alloc_contract_spec.spl` covers the DMA syscall
  result layout used by the pure Simple NVMe driver and VFS adapter.
- `test/unit/os/kernel/types/device_mem_types_spec.spl` covers DeviceGrant
  BAR/IRQ/DMA/IOMMU token metadata, and the NVMe storage model spec covers using
  that label for a user-assigned namespace lease.
- `test/unit/os/kernel/boot/boot_fs_mount_acceptance_spec.spl` covers the
  provider-neutral boot mount path for NVFS, DBFS, and FAT32 over the same
  `BlockDevice` interface and keeps production acceptance fail-closed on
  non-pure storage evidence.
- `test/unit/os/services/vfs/vfs_boot_nvme_lease_spec.spl` covers the
  pure-Simple boot FAT32 lease helper and rejects invalid namespace geometry
  before mounting.
- `test/unit/os/drivers/nvme/nvme_transfer_command_spec.spl` covers shared
  syscall-free NVMe transfer command construction, namespace-aware read/write
  command construction, namespace-aware flush construction, zero-count
  rejection, NLB limit rejection, DMA pointer validation, and completion-status
  decoding.
- `test/unit/os/drivers/nvme/nvme_driver_probe_contract_spec.spl` covers that
  the driver exposes namespace-aware identify/read/write/flush methods, stores
  identified NSID geometry, creates bounded user data queues for assigned
  namespaces, and keeps non-identified namespaces fail-closed before hardware
  submission.
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
