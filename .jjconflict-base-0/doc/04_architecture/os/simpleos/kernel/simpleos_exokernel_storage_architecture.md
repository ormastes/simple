# SimpleOS Exokernel Storage And Device Architecture

**Status:** Draft implementation target.

**Purpose:** Define how SimpleOS should expose NVMe namespaces, partitions,
directories, queues, and other devices while keeping SimpleOS native APIs
async-first and capability-backed.

## Doctrine

SimpleOS provides POSIX compatibility, but POSIX paths are not the authority
primitive. Native SimpleOS drivers, services, and apps should use explicit
capability handles. POSIX directories and file descriptors are compatibility
views over those handles.

The storage/device model follows an Arrakis-style exokernel split:

- the kernel owns protection primitives: address spaces, capabilities, IPC
  credentials, IRQ delivery, DMA/IOMMU mappings, and revocation;
- `pcimgr` and the device manager own discovery, driver matching, and raw PCI
  device assignment;
- the NVMe driver and storage authority own admin commands, namespace
  discovery, partition scanning, queue allocation, and crash/recovery rules;
- apps and library OS code receive bounded storage, mount, and queue
  capabilities instead of raw MMIO or DMA authority.

The important rule is that exokernel does not mean "apps get raw hardware."
It means apps may control policy only after the trusted control plane has made
misuse impossible.

## Prior Art

This design is based on:

- MIT Exokernel/Xok/ExOS: kernel securely multiplexes hardware while library
  OS code implements abstractions and policy;
- XN protected disk ideas: storage policy can move out of the kernel only if
  ownership, metadata safety, cache coherence, and reuse rules stay protected;
- Arrakis: OS control plane grants bounded data-plane access to virtualized
  device resources;
- seL4 and Fuchsia/Zircon: authority is explicit in kernel-held capabilities or
  handles with rights;
- Linux blk-mq: software queues feed hardware dispatch queues, and completion
  order is not guaranteed by the block layer;
- Linux VFIO/IOMMU: direct device access is safe only at the hardware isolation
  granularity, often the IOMMU group rather than one PCI function;
- NVMe: namespaces are controller-visible storage objects and I/O queues are
  controller-local submission/completion resources, not security domains.

## NVMe Namespace And Partition Model

SimpleOS must treat an NVMe namespace as the first storage object below a
controller. Namespace IDs are controller-local and should not be used as durable
global identity by themselves.

Boot discovery target:

1. initialize PCI and BAR access through `pcimgr`;
2. create NVMe admin queue `QID 0`;
3. create reserved system I/O queue `QID 1`;
4. enumerate active namespace IDs;
5. identify every namespace and capture LBA size/count plus UUID/EUI/NGUID
   descriptors where available;
6. register raw namespace devices such as `/dev/nvme0n1` and `/dev/nvme0n2`;
7. scan GPT/MBR inside each namespace;
8. register partitions such as `/dev/nvme0n1p1`;
9. mount root and service filesystems by UUID, label, or explicit boot config.

The current single-namespace path remains transitional until all I/O APIs carry
an explicit namespace or block-device identity.

## Queue Policy

NVMe queue IDs are not security boundaries. They are scheduling and submission
resources. Security comes from capabilities, range checks, DMA ownership, and
IOMMU domains.

SimpleOS queue layout:

| Queue | Role | Allowed traffic |
| --- | --- | --- |
| `QID 0` | Admin | Controller setup, Identify, feature setup, queue create/delete. |
| `QID 1` | System I/O | Discovery reads, partition scans, mount probes, metadata recovery, emergency flush, shutdown. |
| `QID 2+` | Data I/O | App, service, and filesystem data traffic after policy assignment. |

Do not allocate one hardware queue per directory by default. Use software queue
contexts for apps, mounts, partitions, and extents, then map those contexts to
hardware queues. Allocate dedicated hardware queues only for trusted,
high-throughput principals when the controller and interrupt budget allow it.

The queue manager owns:

- queue creation and teardown;
- queue depth and fullness accounting;
- command ID allocation;
- completion routing by `(queue_id, command_id)`;
- timeout and cancellation policy;
- caller accounting and fairness;
- flush, FUA, and ordering barriers.

## Directory And Partition Access

"Full access to a partition directory" is represented as a mount capability
backed by a partition capability:

```text
StoragePartition("/dev/nvme0n1p4", read|write)
Mount("/data/app", read|write|mount)
```

Other directories receive narrower caps:

```text
Mount("/etc/app", read)
Mount("/tmp/app", read|write)
BlockDevice("/dev/nvme0n1", read)       # diagnostic tools only
```

Apps should normally see mounted namespaces and directories, not raw
controllers. Native SimpleOS services may request lower-level handles such as
`StorageExtent` and `IoQueue` when they need database-style or library-OS
storage policy.

## Capability Surface

The kernel capability enum now names the authority boundaries needed by this
architecture:

- `DeviceEnumerate`
- `DeviceGrant`
- `DeviceBarMap`
- `DeviceDma`
- `IommuDomain`
- `BlockDevice`
- `StorageNamespace`
- `StoragePartition`
- `StorageExtent`
- `Mount`
- `IoQueue`

Normal apps should receive storage and mount caps. Driver capsules may receive
device caps. Trusted high-performance services may receive queue caps after
the storage authority has pinned their storage bounds and DMA domain.

## Other Devices

The same pattern applies to NICs, GPUs, USB controllers, and future hardware:

1. `pcimgr` discovers devices and owns raw PCI access.
2. Driver capsules receive only the BAR, IRQ, DMA, and IOMMU caps they need.
3. Apps receive service handles or data-plane queue/filter caps.
4. Without IOMMU isolation, untrusted apps stay behind broker drivers and
   bounce buffers.

The safe device assignment unit is the IOMMU group, not necessarily one PCI
function. SimpleOS should model IOMMU groups before supporting direct device
assignment to untrusted code.

## MDSOC Placement

This storage/device architecture is MDSOC-only in kernel and drivers, and
MDSOC+ in services/apps:

- kernel: capability objects, IPC credentials, IRQ, DMA, IOMMU, revocation;
- drivers: NVMe controller and queue mechanics;
- services: storage authority, devfs, VFS, mount manager, queue broker;
- userlib: async-first native storage and device facades;
- POSIX/libc: sync wrappers over native async file and device services.

Synchronous POSIX file APIs must block on native async storage operations. They
must not become independent storage state owners.

## BDD Acceptance Criteria

```text
Given an NVMe controller with namespaces 1 and 2
When the storage authority boots
Then it registers /dev/nvme0n1 and /dev/nvme0n2 separately
And namespace identity includes controller id, nsid, LBA geometry, and stable descriptors when present

Given a namespace with two GPT partitions
When partition scan completes
Then /dev/nvme0n1p1 and /dev/nvme0n1p2 exist
And all partition I/O is range-checked before reaching the NVMe driver

Given queue ids 0, 1, and 2
When queue policy is queried
Then 0 is admin, 1 is system, and 2 is data
And app data traffic cannot use the admin or system queues

Given an app with Mount("/data/app", read|write)
When it opens /data/app/db
Then VFS authorizes the open through the mount cap
And the app receives no raw DeviceBarMap or DeviceDma authority

Given a trusted driver capsule for an NVMe controller
When pcimgr grants the device
Then the grant contains nonzero BAR, IRQ, DMA, and IOMMU tokens where supported
And MapBar and AllocDma reject requests that do not present matching tokens
```

## Implementation Sequence

1. Keep the queue constants and capability variants wired in
   `capability_types.spl`.
2. Replace broad `PortIO(0,0)` and `Mmio(0,0)` device gates with
   object-specific `Device*` caps.
3. Make manifests parse storage/device cap strings into `CapabilityKind`.
4. Add namespace enumeration to NVMe and carry NSID through all read/write/flush
   paths.
5. Add a canonical block-device identity and geometry layer above NVMe.
6. Add `PartitionBlockDevice` with GPT/MBR scan and LBA remapping.
7. Teach devfs to register namespace and partition instances.
8. Make VFS/devfs open and lookup paths enforce caller credentials and caps.
9. Replace copied/polling async NVMe completions with queue-owned command IDs
   and completion routing.
10. Add IOMMU-aware DMA handles before any app-visible direct queue fast path.
