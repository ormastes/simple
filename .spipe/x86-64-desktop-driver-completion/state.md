# SStack State: x86-64-desktop-driver-completion

## User Request
> next task from the plan — x86_64_desktop_driver_completion (P0 driver matrix/discovery/storage, P1 display/input/network, P2 verification)

## Task Type
feature

## Refined Goal
> Implement x86_64 desktop driver completion infrastructure: driver acceptance matrix with capability summary, PCI resource ownership, storage DMA unification, display mode reporting, input enumeration, network capability exposure, and verification specs.

## Acceptance Criteria
- [ ] AC-1: Driver acceptance matrix — mandatory driver set (UEFI, ACPI, PCI, NVMe/VirtIO-BLK, framebuffer/BGA/VirtIO-GPU, PS/2, virtio-net) with pass/fail status
- [ ] AC-2: Capability summary — serial output: platform, storage, display, input, network, DMA, interrupt mode
- [ ] AC-3: PCI resource ownership — BAR, IRQ, DMA, device class records before driver bind
- [ ] AC-4: Platform discovery — UEFI/OVMF boot path, ACPI RSDP/MADT parse status, PCI device count, interrupt mode
- [ ] AC-5: Storage DMA unification — NVMe/VirtIO-BLK read/write via shared DMA descriptor, timeout/completion markers
- [ ] AC-6: Display mode reporting — framebuffer/bga/virtio_gpu with accelerated=false unless VirtIO-GPU command completion observed
- [ ] AC-7: Input device enumeration — PS/2 keyboard/mouse acceptance, xHCI non-blocking diagnostics
- [ ] AC-8: Network capability — virtio-net init, MAC reporting, queue setup, capability tier
- [ ] AC-9: False-claim rejection — resident launch fallback, hidden DMA fallback, false acceleration all fail acceptance
- [ ] AC-10: Verification spec — 20 tests covering matrix, summary, PCI, storage, display, input, network, rejection

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-18
- [x] 2-4 — skipped (plan doc comprehensive)
- [x] 5-implement (Engineer) — 2026-05-18
- [x] 6-refactor (Tech Lead) — 2026-05-18
- [x] 7-verify (QA) — 2026-05-18
- [x] 8-ship (Release Mgr) — 2026-05-18

## Phase Outputs

### 1-dev
10 ACs across P0/P1/P2. Existing: drivers/, qemu_runner.spl, framebuffer/, virtio_gpu.spl, nvme/, virtio_blk.spl, netstack/.

### 5-implement
5 parallel Sonnet agents. 4 source + 1 test:
- src/os/drivers/x86_64/driver_acceptance.spl — DriverEntry + DriverMatrix + CapabilitySummary
- src/os/drivers/x86_64/platform_discovery.spl — PciResource + PciResourceTable + BootDiscovery + DiscoveryLog
- src/os/drivers/x86_64/device_reporting.spl — StorageDmaResult + DisplayReport + InputDevice + FalseClaimCheck
- src/os/drivers/x86_64/net_driver_report.spl — VirtioNetInit + NetDriverCapability + AcceptanceGate + AcceptanceReport
- test/unit/os/x86_64_driver_spec.spl — 20 tests

### 7-verify
20/20 tests PASS.
