<!-- codex-research -->
# Requirements: x86_64 Desktop Driver Completion

## Selected Option

Feature Option B: Balanced QEMU Completion Plus Hardware-Alpha Hooks.

## Requirements

- REQ-X64DRV-001: The x86_64 desktop driver milestone must keep QEMU desktop completion as the primary acceptance target.
- REQ-X64DRV-002: The primary driver matrix must cover UEFI/OVMF boot, ACPI/MADT discovery evidence, PCI enumeration evidence, storage, display, input, and network.
- REQ-X64DRV-003: Storage completion must prove NVMe or VirtIO-BLK can back the desktop disk path and expose VFS-readable app bytes without special host bridges.
- REQ-X64DRV-004: Display completion must distinguish framebuffer/BGA fallback from VirtIO-GPU acceleration and must not claim acceleration without command-completion evidence.
- REQ-X64DRV-005: Input completion for the QEMU milestone may use PS/2 keyboard and mouse to drive the desktop shortcut path.
- REQ-X64DRV-006: Network completion must initialize virtio-net and expose a bounded SimpleOS netstack smoke path.
- REQ-X64DRV-007: Driver output must include non-blocking hardware-alpha capability hooks for MSI/MSI-X, IOMMU, and xHCI enumeration diagnostics.
- REQ-X64DRV-008: Advanced physical-hardware support is not required to pass the QEMU desktop driver milestone unless explicitly selected later.

