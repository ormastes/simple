<!-- codex-research -->
# Local Research: SimpleOS CXL and Device-Process Architecture

Date: 2026-08-02  
Lane: `simpleos_cxl_device_process_architecture`  
Status: research complete; requirements selection pending

## Purpose

This is the next repository-grounded research document after
`doc/01_research/os/simpleos/platform/simpleos_l4_exokernel_platform.md`. It
does not replace that document. It narrows the earlier L4/exokernel direction
to device processes, resource protection, data queues, CXL, xHCI/HID, HDA, QEMU,
and distributed MPU/MCU placement.

## Reviewed direction

The recommended architecture is sound with one important wording correction:
SimpleOS already has functional process, notification, capability, driver, and
QEMU mechanisms, but their enforcement and ownership are incomplete. The work
should harden and compose those mechanisms rather than create a second CXL-only
kernel or duplicate capability stack.

The target split is:

- the kernel owns protection, identity, mappings, interrupt routing, DMA/IOMMU,
  revocation, scheduling, and minimal IPC;
- user-space driver processes and services own binding, protocol, policy,
  topology, recovery policy, and client APIs;
- hardware-owning drivers use `HostIsolated` by default;
- colocation is an explicit, profiled exception;
- `CoprocessorRemote` and `DeviceResident` are explicit placements, never
  inferred merely from CXL presence.

## Evidence matrix

| Area | Repository evidence | Assessment |
|---|---|---|
| Threads and VM spaces | `src/os/kernel/types/thread_types.spl`, `src/os/kernel/types/vmspace_types.spl`, `src/os/kernel/scheduler/process_table_extended.spl`, `src/os/kernel/memory/vmm_address_space.spl`, `src/os/kernel/scheduler/address_space_switch.spl` | Implemented in parts. Fresh address spaces and architecture switching exist, but there is no single enforced `Process -> VmSpace -> Thread -> CapabilitySpace -> ResourceLease` lifetime. |
| IPC | `src/os/kernel/ipc/ipc.spl`, `src/os/kernel/ipc/syscall_ipc.spl`, `src/os/kernel/types/endpoint_types.spl`, `src/os/kernel/ipc/message_buffer.spl` | Bounded named/raw-port IPC exists: 64 messages, 4 KiB per copied payload, and 64 KiB per-port owned payload. Sender authentication and capability transfer across address spaces remain incomplete. |
| Notifications | `src/os/kernel/types/notification_types.spl`, `src/os/kernel/ipc/notification.spl`, `src/os/kernel/ipc/syscall_notif.spl` | Signal/wait/poll mechanisms exist, but global IDs are not yet owner-authorized `NotificationCapability` handles. |
| Capabilities | `src/os/kernel/types/capability_types.spl`, `src/os/kernel/ipc/capability.spl` | Logical generation, delegation, and transitive revocation exist. They do not yet guarantee removal of BAR mappings, IRQ routes, DMA mappings, or device attachments. |
| Driver grants | `src/os/services/driver_supervisor/resource_grant.spl`, `src/os/services/driver_supervisor/grant_broker.spl`, `src/os/kernel/types/device_mem_types.spl`, `src/os/kernel/ipc/syscall_device.spl` | Grant tokens are bookkeeping, not a complete security boundary. The broker has four flat driver slots; physical BAR/DMA values remain exposed; revoke clears logical state without guaranteed hardware teardown. |
| Driver runtime | `src/lib/nogc_async_mut/driver/manifest.spl`, `src/lib/nogc_async_mut/driver/loader.spl`, `src/os/lib/driver_runtime/lifecycle.spl`, `src/os/lib/driver_runtime/event_loop.spl`, `src/os/services/driver_supervisor/supervisor.spl` | Static/dynamic manifest loading and lifecycle/supervision foundations exist. `DriverManifestV2`, `DriverPlacement`, `DeviceNode`, bind rules, child publication, `ResourceLease`, and the unified device queue contract do not. |
| PCI | `src/os/drivers/pci/pci.spl`, `src/os/drivers/pci/pci_provider.spl`, `src/os/drivers/pci/pci_bar64.spl`, `src/os/services/pcimgr/pcimgr.spl` | q35 configuration I/O, ECAM addressing, enumeration, and BAR decoding exist. Scanning is duplicated in the kernel device syscall path. No PCIe extended-capability, DVSEC/DOE, CEDT/CFMWS, component-register, mailbox, HDM decoder, region, or CXL RAS implementation was found under `src/os`. |
| DMA/IOMMU | `src/os/kernel/ipc/dma_alloc_contract.spl`, `src/os/kernel/memory/memory_dma_pages.spl`, device syscall and grant files above | DMA ownership/accounting exists, but callers still receive physical addresses. No complete IOVA page-table, device attachment, fault queue, interrupt-remapping, or IOMMU-backed revocation path was found. |
| xHCI/USB/HID | `src/os/drivers/usb/xhci_driver.spl`, `xhci_trb.spl`, `xhci_enum.spl`, `usb_hid_input_backend.spl`, `usb_hid_bridge.spl` | Functional controller/enumeration/input paths exist but remain kernel-coupled. xHCI imports kernel MMIO, PMM, and PCI, rescans PCI, and uses physical rings. HID assumes fixed boot keyboard and mouse reports instead of a general report-descriptor parser. |
| HDA/audio | `src/os/drivers/audio/hda_controller.spl`, `hda_dma_resources.spl`, `hda_pci_binding.spl`, `hda_codec_probe.spl` | Controller, DMA, PCI binding, and codec probe code exist, but direct MMIO, physical DMA, runtime PCI calls, and explicit probe stubs prevent a true isolated-driver claim. An unrelated active audio lane currently owns dirty audio files. |
| QEMU evidence | `src/os/qemu_runner.spl`, `src/os/_QemuRunner/scenario_catalog.spl`, `test/03_system/os/qemu/os/common/qemu_os_harness.spl`, `scripts/check/check-simpleos-usb-xhci-qemu.shs`, `scripts/check/check-simpleos-io-audio-qemu.shs` | Scenario and QMP foundations exist. There is no integrated CXL topology/RAS suite, driver-process crash gate, or unified evidence bundle. Existing xHCI and audio wrappers contain seed/stub or synthetic-marker allowances and cannot prove the target boundary. |
| CXL | no matching implementation under `src/os` | Proposal-only. The first implementation lane must start at PCIe extended capabilities and ACPI CEDT, not at a memory-tier policy API. |

## Architectural gap that blocks every real user driver

The missing unit is not another driver module. It is an enforceable lease:

```text
Process
  -> VmSpace
  -> CapabilitySpace
  -> ResourceLease(generation)
       -> DeviceMemCapability
       -> IrqCapability
       -> DmaWindowCapability / IoAddressSpace / IommuDomain
       -> SharedRegionCapability
       -> NotificationCapability
       -> ResetCapability
```

Revocation must remove authority and hardware effects. Clearing a token or a
counter is insufficient if the process can still access a mapping, receive an
interrupt, or leave a device able to DMA.

## Placement vocabulary

| Placement | Meaning | Initial status |
|---|---|---|
| `KernelBootstrap` | Minimal hardware needed before user space | retained but tightly bounded |
| `HostIsolated` | Driver runs on the host CPU in its own process/driver host | default target |
| `HostColocated` | Trusted driver components share a host after profiling | optional, policy-gated |
| `CoprocessorRemote` | Driver runs on another programmable CPU and is proxied over a transport | blocked pending target transport/runtime proof |
| `DeviceResident` | Signed driver/service code executes in endpoint firmware/runtime | blocked pending programmable endpoint, secure loading, isolation, interrupts, DMA, transport, watchdog, reset, update, and attestation proof |

CXL is independent of this placement classification. A Type 3 memory device is
not a processor. For the Type 3 host-to-host queue case, the memory mode should
be named `CxlHostMapped`, not `CxlCoherent`, so the ABI does not imply a device
consumer or emulated coherency guarantee. Reserve `CxlDeviceCoherent` for a
future proved Type 1/2 endpoint runtime.

## Correct dependency order

1. Freeze versioned driver/device/lease/queue contracts and threat model.
2. Authenticate IPC identity and capability transfer.
3. Make BAR, IRQ, DMA, IOMMU, reset, and teardown capability-backed.
4. Prove a synthetic isolated driver loses all authority on crash and restarts
   with a new generation.
5. Migrate xHCI, USB bus, HID, and input delivery as the first real vertical
   slice.
6. Add PCIe/CXL discovery and QEMU topology evidence.
7. Add Type 3 mailbox/HDM/region/RAS support.
8. Add a CXL-host-mapped queue only after DRAM queue recovery is established.
9. Keep UNO Q physical, real CXL hardware, Type 1/2, and device-resident rows
   blocked until their target environments exist.

## Risks requiring explicit gates

- Existing process, notification, and capability mechanisms may be duplicated
  unless one contract owner freezes adapters and migration rules.
- `xhci_enum.spl` currently crosses controller and USB-bus ownership and must be
  split by the merge owner before parallel H/I implementation.
- Driver teardown spans IPC, scheduler, device syscalls, IOMMU, IRQ, and devmgr;
  no single implementation agent may silently own all of it.
- Security/fuzz work cannot be deferred to the last wave; adversarial gates
  apply to every resource-boundary merge.
- The current dirty audio lane must be reconciled before an HDA migration agent
  receives file ownership.
- QEMU functional evidence must never be presented as real coherence timing,
  fabric management, multi-host, or hardware performance evidence.

## Research conclusion

Adopt the hybrid L4/exokernel direction, but implement it as a hardening and
composition of existing SimpleOS mechanisms. The first milestone is the real
user-driver protection boundary; the first physical vertical slice is isolated
xHCI through HID and compositor input; the first CXL milestone is CXL 2.0 Type
3 discovery/regions/RAS in QEMU with an extensible CXL 4.0 capability model.
