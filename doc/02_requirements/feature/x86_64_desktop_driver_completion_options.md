<!-- codex-research -->
# Feature Options: x86_64 Desktop Driver Completion

## Option A: QEMU Desktop Driver Minimum

Description: Complete the x86_64 desktop driver matrix for QEMU only: OVMF/UEFI, ACPI/MADT evidence, PCI enumeration, NVMe or VirtIO-BLK disk, framebuffer/BGA or VirtIO-GPU display, PS/2 input, and virtio-net smoke.

Pros:
- Fastest path to a real complete desktop milestone.
- Aligns with existing QEMU, desktop, disk, and driver code.
- Keeps real-hardware xHCI/IOMMU/MSI complexity out of the first acceptance gate.

Cons:
- Does not claim physical PC readiness.
- USB and IOMMU remain follow-on work.

Effort: L, 10-18 files across QEMU runner, driver summaries, storage/display/network tests, and docs.

## Option B: Balanced QEMU Completion Plus Hardware-Alpha Hooks

Description: Complete the QEMU desktop driver matrix and add non-blocking hardware-alpha hooks for MSI/MSI-X reporting, IOMMU capability reporting, and xHCI enumeration diagnostics.

Pros:
- Still keeps QEMU desktop completion central.
- Creates clear runway toward real hardware.
- Gives driver code truthful capability output for advanced features.

Cons:
- Larger scope and more integration risk.
- Hardware hooks may initially report unsupported on most lanes.

Effort: XL, 18-30 files across driver capability APIs, PCI/ACPI, xHCI, QEMU tests, and docs.

## Option C: Physical PC Driver Alpha

Description: Treat physical x86_64 desktop boot as the driver milestone: UEFI on selected machines, ACPI/PCI/APIC/MSI, NVMe, xHCI keyboard/mouse, framebuffer/GOP, and optional virtio only for CI.

Pros:
- Most ambitious and closest to real desktop OS expectations.
- Forces robust firmware and hardware error handling early.

Cons:
- High hardware variability and debugging cost.
- Harder to make deterministic in CI.
- Delays process-backed desktop and QEMU completion work.

Effort: XXL, 30+ files plus hardware test matrix and manual validation.

## Recommendation

Option B is the best default if the goal is “complete desktop OS for x86_64” without pretending QEMU-only work equals real-PC support. Option A is better if the immediate goal is a passing CI milestone.

