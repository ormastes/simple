<!-- codex-design -->
# Architecture: x86_64 Desktop Driver Completion

## Boundary

The x86_64 desktop driver layer is a capability-backed service boundary between kernel-owned platform resources and user-visible desktop services.

- Kernel owns ACPI tables, PCI enumeration, BAR mapping, IRQ routing, DMA allocation, and task cleanup.
- Driver capsules own device-specific queues and completion state.
- Services expose VFS, display, input, and network APIs to desktop apps.
- Desktop apps must never access raw BARs, IRQs, or DMA descriptors.

## Driver Matrix

- Platform: UEFI/OVMF, ACPI RSDP/MADT, APIC/IOAPIC, PCI.
- Storage: NVMe primary for x86_64 desktop disk; VirtIO-BLK allowed fallback.
- Display: framebuffer/BGA fallback; VirtIO-GPU accelerated path only when command completion is verified.
- Input: PS/2 keyboard/mouse for QEMU milestone; xHCI diagnostic-only until hardware alpha.
- Network: virtio-net plus SimpleOS netstack smoke.

## Capability Summary

Each driver family reports a stable summary during boot:

- device id and driver name
- DMA mode and hidden-copy status
- interrupt mode: `interrupt`, `polling`, or `unsupported`
- acceleration state where applicable
- last init/completion error

## Safety Rules

- No driver may claim DMA if it did not receive a kernel-owned DMA descriptor.
- No display driver may claim acceleration for framebuffer/BGA writes.
- Polling is acceptable only when reported as polling.
- Device resources are released on task/driver cleanup.
- Advanced hardware features such as IOMMU, MSI/MSI-X, RDMA, and SR-IOV are capability-gated and not default desktop requirements.

