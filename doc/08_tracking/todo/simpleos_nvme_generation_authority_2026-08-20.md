# SimpleOS NVMe generation authority

**Status:** PARTIAL — in-boot source landed; filesystem promotion remains blocked

**Owner:** OS VFS/NVMe storage lane; merge owner `/root`

The OS layer now contains `NvmeDeviceGenerationAuthorityV1` and opaque
`NvmeDeviceGenerationTokenV1` in
`src/os/services/vfs/nvme_device_generation_authority_v1.spl`. The authority
is a marker over one private mutex-backed process registry, with bounded token
slots, exact controller/namespace/lease binding checks, and typed
stale/replay/invalid-token errors. Creating another marker cannot fork state.

`NvmeDriver` now owns a process-lifetime `device_generation` and a trusted
PCI/controller/namespace `device_identity`. The generation advances from the
process-global counter only after successful grant-based initialization, so a
fresh driver value cannot restart the ABA fence at generation one; baremetal
initialization remains unbound. The durability adapter consumes an authority
token rather than a caller-created binding.

The canonical VFS mount path does not yet issue the authority token or wire
the durable adapter. The adapter contains current-incarnation checks for each
read/write/flush, but all durable I/O remains unavailable because the driver
does not yet serialize controller reset/reinitialization against adapter I/O
under one shared owner lock; ordered I/O returns the typed
`ResetNotSerialized` refusal before submitting work. A consumed token is not
an I/O capability. No crash persistence or cross-reboot guarantee is claimed;
this generation is only an in-boot stale-binding fence.

The oversized driver owner is now split into cohesive method-extension modules:
`driver_operations.spl` retains lifecycle/incarnation and bounded ownership,
while `queue_creation.spl`, `sector_io.spl`, `bulk_io.spl`, and
`probe_and_query.spl` hold stateless operations over that same `NvmeDriver`.
Every source is below 800 lines; no second controller, reset, or generation
authority was introduced. Submission sentinel failures and 4KiB LBA, byte
length, and DMA-address overflow now reject before waiting or MMIO submission.
Constructing a value no longer clears the process-wide bounded queue ownership
registry, so a copied/fresh driver value cannot erase existing assignments.

Serialization remains deliberately unavailable. The SimpleOS implementation
of `spl_mutex_create/lock/unlock` in
`examples/09_embedded/simple_os/arch/x86_64/boot/primitives.c` is explicitly a
single-threaded no-op stub: lock does not establish exclusion. Importing the
hosted raw-mutex facade would therefore create false durability evidence on
SimpleOS. `nvme_reset_serialized_with_io()` remains `false` until either that
provider supplies real exclusion on every admitted SimpleOS target, or reset,
write, and same-queue flush are routed through one enforced single-owner
service with a behavioral non-interleaving model.

The alternative primitives were audited and are also insufficient:

- `std.nogc_sync_mut.atomic.AtomicI64.compare_exchange` delegates to
  `rt_atomic_int_compare_exchange`. The SimpleOS x86 provider in
  `boot/rt_extras.c` labels the family “single-core baremetal — no actual
  contention” and implements compare-exchange as an ordinary pointer load and
  conditional store. No corresponding real provider exists for the inspected
  ARM/RISC-V SimpleOS paths.
- `std.nogc_sync_mut.io.thread.atomic_i64_compare_exchange` accepts an `i64`
  value, returns a replacement value, and does not mutate shared storage.
- kernel interrupt-disable and `percpu_preempt_disable` surfaces are
  kernel/CPU-local. The NVMe driver is a user-space driver, and disabling one
  CPU's interrupts/preemption would not exclude another CPU or task owner.
- the kernel syscall shim itself records that multi-core access still needs
  spinlocks (`src/os/kernel/abi/syscall_shim.spl`, Wave 10E); there is no
  scheduler exclusion syscall available to this driver.

The exact missing capability is therefore an atomic compare-exchange over a
Simple-owned shared word with acquire/release ordering on every admitted
SimpleOS architecture, or an equivalent scheduler-owned exclusion syscall.
`nvme_reset_serialization_blocker()` reports
`missing-simpleos-atomic-compare-exchange-or-scheduler-exclusion`. The caller
path is `NvmeDurableBlockAdapter.write_sector`, `read_sector`, and
`_flush_ordered_typed` -> `nvme_reset_serialized_with_io`; each returns
`ResetNotSerialized` before durable submission/flush. Contention/acquire-failure
transition specs remain inapplicable until an acquisition primitive exists;
adding a value-only model would not constitute executable exclusion evidence.

The PCI BDF is the only trusted hardware identity currently available in the
driver. `NvmeNamespaceIdentity.controller_id` is a logical lease/queue field;
there is no canonical PCI-BDF-to-controller-id source mapping yet, so token
issuance rejects zero/incomplete lease bindings and does not promote mounts.

**Unblock condition:** add one real shared lifecycle/I/O owner lock (not the
current SimpleOS no-op mutex provider) spanning `NvmeDriver`
reset/reinitialization and durable write+same-queue-flush, then
issue a token from the successful `NvmeDriver` incarnation and exact lease
identity before constructing the adapter. Crash-cut/recovery evidence remains
a separate requirement before any cross-reboot durability claim.

**Resume command:** run the focused authority spec with the admitted
source-matched Simple runtime, then the VFS durability and filesystem
conformance rows. No runtime or hardware evidence is claimed by this update.
