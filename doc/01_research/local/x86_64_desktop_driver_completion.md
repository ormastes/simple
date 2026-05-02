<!-- codex-research -->
# Local Research: x86_64 Desktop Driver Completion

## Scope

Make x86_64 SimpleOS driver support sufficient for a complete QEMU desktop OS milestone. This research consolidates existing storage, display, input, network, PCI, ACPI, DMA, and driver-supervision work into one driver completion track.

## Existing Code

- Platform discovery and interrupt substrate exist under `src/os/kernel/acpi/`, `src/os/kernel/interrupts/`, and `src/os/drivers/pci/pci.spl`.
- Driver families already exist:
  - storage: `src/os/drivers/nvme/`, `src/os/drivers/virtio/virtio_blk.spl`
  - display: `src/os/drivers/framebuffer/`, `src/os/drivers/gpu/`, `src/os/drivers/virtio/virtio_gpu.spl`
  - input: `src/os/drivers/input/ps2_keyboard.spl`, `ps2_mouse.spl`
  - network: `src/os/drivers/virtio/virtio_net*.spl`, `src/os/services/netstack/`
  - USB: `src/os/drivers/usb/xhci_*.spl`
  - supervision/services: `src/os/services/pcimgr/`, `src/os/services/display/`, `src/os/services/driver_supervisor/`
- Desktop and compositor code already has framebuffer, hosted, input, capture, and WM surfaces under `src/os/compositor/`, `src/os/desktop/`, and `src/os/gui/`.
- QEMU runner now has a UEFI-oriented x86_64 desktop scenario surface (`x64-desktop-uefi`) and existing disk/full-stack lanes.

## Existing Requirements And Plans

- `doc/04_architecture/driver_architecture.md` defines pure-Simple driver direction, static/dynamic driver modes, SFFI boundaries, and gaps for DMA coherent allocation, runtime loader, probe/bind DSL, and `.drv_manifest`.
- `doc/02_requirements/feature/driver_dma_direct_io.md` and `doc/02_requirements/nfr/driver_dma_direct_io.md` define the common DMA descriptor and no-hidden-copy rules.
- `doc/02_requirements/feature/driver_display_acceleration_boundary.md` and `doc/02_requirements/nfr/driver_display_acceleration_boundary.md` distinguish framebuffer fallback from real VirtIO-GPU acceleration and prohibit false VGA DMA claims.
- `doc/03_plan/agent_tasks/dma_file_vga_driver_remaining_2026-04-21.md` identifies P0 shared DMA safety, P1 block direct I/O, P1 display acceleration, and P2 performance proof.
- `doc/03_plan/agent_tasks/net_acceleration_remaining_2026-04-21.md` identifies P0 socket-visible TCP correctness, P1 backend capabilities, P1 packet I/O, and P2 hardware acceleration experiments.
- `doc/03_plan/agent_tasks/simpleos_missing_os_subsystems_report.md` marks file I/O, scheduler/process isolation, executable loading, system API/lib, and dynamic loading as partial, with desktop app launch still depending on fallback bridges.

## Gaps For A Complete x86_64 Desktop Driver Milestone

- No single driver acceptance matrix says which devices are mandatory for the x86_64 desktop milestone.
- PCI/ACPI/APIC discovery exists, but MSI/MSI-X, interrupt routing evidence, and device-resource ownership are not yet the primary acceptance contract.
- DMA APIs exist, but driver families do not share one audited descriptor/result shape everywhere.
- Storage has NVMe and VirtIO-BLK code, but the desktop launch path still needs reliable generic VFS byte streams and driver-backed app reads.
- Display has framebuffer/BGA and VirtIO-GPU code, but the acceptance lane must label framebuffer fallback versus accelerated GPU truthfully.
- Input currently relies on PS/2 coverage for QEMU desktop; USB/xHCI should be a follow-on, not a blocker for QEMU completion.
- Network has virtio-net and a SimpleOS netstack, but desktop completion needs a minimal socket smoke and capability reporting, not RDMA/SR-IOV.

## Recommended Local Direction

Use a QEMU-first driver matrix:

- P0 platform: UEFI/OVMF + ACPI RSDP/MADT + PCI enumeration + IOAPIC/APIC routing evidence.
- P0 storage: NVMe or VirtIO-BLK can mount the desktop disk and read packaged apps through VFS without resident fallback.
- P0 display/input: framebuffer/BGA or VirtIO-GPU provides desktop-ready pixels; PS/2 input drives shortcuts.
- P1 network: virtio-net can complete DHCP/static config equivalent smoke, ARP/IPv4/ICMP/TCP loop or user-net smoke, and report backend capabilities.
- P1 safety: all DMA-capable drivers use the shared DMA contract and report fallback copies explicitly.
- P2 real hardware: xHCI, MSI/MSI-X, IOMMU, and broader PCI device quirks become alpha hardware expansion after QEMU completion.

