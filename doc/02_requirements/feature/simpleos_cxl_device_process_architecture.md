# Feature Requirements: SimpleOS CXL Device Processes

Selected: 2026-08-02  
Selection: **Feature Bundle A — staged hybrid**  
Research: `doc/01_research/local/simpleos_cxl_device_process_architecture.md`
and `doc/01_research/domain/simpleos_cxl_device_process_architecture.md`

## Goal

Implement a hybrid L4-style microkernel/exokernel device architecture in which
the kernel enforces resource protection and isolated user processes implement
device protocols and policy, with CXL Type 3 support following a proved xHCI
device-process boundary.

## Requirements

- **REQ-001 — Protection/policy split:** The kernel shall own process identity,
  VM spaces, scheduling, capability enforcement, MMIO mapping, IRQ routing,
  DMA/IOMMU programming, reset authority, revocation, and minimal IPC. User
  services shall own binding, topology, protocols, placement, and policy.
- **REQ-002 — Unified process lifetime:** A hardware driver shall have an
  enforceable `Process -> VmSpace -> CapabilitySpace -> Thread[] ->
  ResourceLease[]` lifetime. Driver termination shall not terminate the kernel
  or unrelated driver processes.
- **REQ-003 — Explicit placement:** `DriverPlacement` shall include
  `KernelBootstrap`, `HostIsolated`, `HostColocated`, `CoprocessorRemote`, and
  `DeviceResident`. `HostIsolated` shall be the hardware-driver default.
  Colocation shall require trust compatibility, restart compatibility,
  `isolation_required=false`, and measured IPC benefit.
- **REQ-004 — Versioned driver contract:** `DriverManifestV2`, `DeviceNode`,
  bind rules, provided/required protocols/resources, lifecycle, placement,
  isolation, restart, resource budgets, watchdog, and firmware identity shall
  be versioned and validated before binding.
- **REQ-005 — Capability resources:** Drivers shall receive revocable
  `DeviceMemCapability`, `IrqCapability`, `DmaWindowCapability`,
  `SharedRegionCapability`, `NotificationCapability`, and `ResetCapability`
  handles rather than globally meaningful physical addresses or process
  pointers.
- **REQ-006 — Safe DMA:** `IoAddressSpace`, `IommuDomain`, `DeviceAttachment`,
  pinned pages, IOVA mapping, synchronization, unmapping, detachment, and fault
  delivery shall be explicit objects. Without a usable IOMMU, SimpleOS shall
  deny unrestricted passthrough and expose only bounded `dma_brokered` buffers.
- **REQ-007 — Authenticated control plane:** Endpoint sender process/thread and
  rights shall come from dispatcher state, not caller-supplied identity. Small
  typed control IPC and asynchronous notification objects shall remain separate.
- **REQ-008 — Shared data plane:** `DeviceQueue` shall use fixed-width fields,
  offsets/buffer IDs, monotonic counters, release/acquire publication, explicit
  backpressure/deadlines, notifications, SPSC edges, and explicit multiplexers.
  It shall never silently overwrite descriptors.
- **REQ-009 — Generation and recovery:** Every `ResourceLease`, queue, and
  descriptor shall carry a generation. Crash, reset, or hot-remove shall stop
  submissions, mask IRQs, revoke mappings/DMA, detach the device, reset when
  possible, rebind at a new generation, and reject stale work.
- **REQ-010 — Unified device graph:** PCI, CXL, USB, HDA, DT platform, and remote
  MCU devices shall use parent-published child `DeviceNode` graphs. Child
  drivers shall receive bounded protocols, not unrestricted parent hardware.
- **REQ-011 — First vertical slice:** The first real device proof shall be
  isolated `xHCI -> USB bus -> generic HID -> inputd -> compositor`, including
  HID and controller crash/recovery, hotplug, and no stuck input state.
- **REQ-012 — CXL capability model:** CXL shall use a revisioned
  `CxlCapabilities` vector, never one support boolean. The model shall represent
  CXL 4.0 features while the first implementation targets QEMU-testable CXL
  2.0 Type 3 discovery, mailbox, HDM/regions, interleave, persistence, RAS,
  poison, and hot-remove (L0-L3).
- **REQ-013 — Honest CXL queue modes:** Type 3 host IPC shall use
  `CxlHostMapped`. `CxlDeviceCoherent` and `DeviceResident` shall remain blocked
  until a programmable endpoint and real coherent device consumer are proved.
- **REQ-014 — CXL queue recovery:** A CXL-backed queue shall retain a non-CXL
  control endpoint, health state, fallback allocator, and relocation protocol.
  Metadata poison shall stop the queue and reconnect validated state in DRAM at
  a new generation.
- **REQ-015 — QEMU evidence boundary:** QEMU shall validate functional topology,
  Type 3 memory, switch/interleave, RAS, poison, hot-remove, USB input, audio,
  crash, and recovery. It shall not be cited as proof of real coherency timing,
  fabrics, multi-host ownership, or hardware performance.
- **REQ-016 — UNO Q truthfulness:** The QRB2210/STM32U585 profiles shall report
  `NoCxl` based on documented interfaces. MCU drivers shall use
  `CoprocessorRemote` proxy nodes only after Bridge/RPC and physical reset/
  reconnect evidence. USB/audio ownership shall follow proved board routing.
- **REQ-017 — Observability:** Device work shall extend the common Debug and
  Evidence Spine with stable build/boot/process/thread/driver/device/lease/
  queue/generation/request/IRQ/trace/span identities, bounded fast events,
  metrics, and safe-whitelist crash bundles.
- **REQ-018 — Unavailable hardware rows:** Real CXL, UNO Q, Type 1/2, and
  `DeviceResident` rows shall remain `blocked` or `unsupported` with target,
  prerequisites, exact resume command, artifacts, owner, and reviewer. They
  shall never be skipped or counted as PASS.

## Implementation order

1. Contract and threat-model freeze.
2. Authenticated process/IPC boundary.
3. MMIO/IRQ/DMA/IOMMU/reset capability enforcement.
4. Synthetic driver crash/revocation/restart proof.
5. Isolated xHCI/HID vertical slice.
6. CXL discovery and Type 3 L0-L3.
7. CXL-host-mapped queue relocation.
8. Physical/future hardware validation without false completion.

## Exclusions

- Automatic memory migration before topology, metrics, and recovery are proved.
- A universal MPMC device ring.
- Treating Type 3 memory as an executable device.
- Declaring QEMU-only results equivalent to real CXL hardware.
