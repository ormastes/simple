<!-- codex-research -->
# Domain Research: x86_64 Desktop Driver Completion

## Driver Baseline For A Practical Desktop OS

A complete QEMU-first x86_64 desktop driver milestone should focus on the smallest real PC-compatible stack that proves the OS can discover devices, move bytes, draw pixels, accept input, and use the network without lying about acceleration.

## Platform And Boot Discovery

- UEFI gives the OS loader environment and boot services for loading the kernel and passing firmware-discovered state. SimpleOS should keep the UEFI/OVMF desktop lane as the acceptance path and treat legacy BIOS/multiboot as compatibility.
- ACPI is the PC platform discovery source for interrupt controllers, timers, and power/platform tables. For x86_64 drivers, ACPI RSDP/MADT evidence should be part of boot logs before PCI device binding.
- APIC/IOAPIC routing is required before desktop drivers can rely on interrupt completion rather than polling-only progress.

Sources: UEFI overview, ACPI 6.6 software model and MADT table list.

## Virtual Device Strategy

- Virtio 1.3 provides standardized virtual PCI devices for block, network, GPU, input, and related transports. QEMU-first desktop completion should prefer virtio where possible because it is portable, testable, and avoids vendor-specific hardware quirks.
- Virtio block/network/GPU should expose explicit capability summaries: queue mode, DMA ownership, polling versus interrupt completion, and fallback-copy behavior.

Source: OASIS Virtio 1.3 specification.

## Storage Strategy

- NVMe is the modern PCIe storage baseline and is appropriate for QEMU desktop disk acceptance. The minimum useful desktop target is controller initialization, queue setup, identify/read/write enough for FAT32/VFS, completion timeouts, and deterministic error reporting.
- VirtIO-BLK remains a useful fallback and cross-architecture comparison path, but x86_64 desktop acceptance should not depend on host-only file bridges.

Source: NVM Express Base Specification 2.1.

## Display And Input Strategy

- Framebuffer/BGA is a valid fallback display path. It must be labeled as fallback, not hardware acceleration.
- VirtIO-GPU is the right QEMU acceleration boundary for command/response DMA and 2D display updates. GPU acceleration should be accepted only when command submission, completion, and DMA summary evidence are visible.
- PS/2 keyboard/mouse is acceptable for the QEMU desktop milestone. xHCI/USB HID should be planned for real-hardware alpha because it adds controller rings, event rings, port reset/enumeration, and HID parsing complexity.

Source: Intel xHCI specification page for USB host controller direction.

## Network Strategy

- VirtIO-net plus the SimpleOS netstack should provide a minimal desktop network proof before advanced acceleration.
- RDMA, SR-IOV, and packet I/O are not desktop-completion blockers. They should stay behind explicit capability flags and benchmark gates.

## References

- UEFI Specification overview: https://uefi.org/specs/UEFI/2.9_A/02_Overview.html
- ACPI Specification 6.6: https://uefi.org/specs/ACPI/6.6/
- ACPI software programming model: https://uefi.org/specs/ACPI/6.6/05_ACPI_Software_Programming_Model.html
- OASIS Virtio 1.3: https://docs.oasis-open.org/virtio/virtio/v1.3/virtio-v1.3.pdf
- NVMe Base Specification 2.1: https://nvmexpress.org/wp-content/uploads/NVM-Express-Base-Specification-Revision-2.1-2024.08.05-Ratified.pdf
- Intel USB/xHCI specifications: https://www.intel.com/content/www/us/en/products/docs/io/universal-serial-bus/universal-serial-bus-specifications.html

