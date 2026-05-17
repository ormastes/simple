# SStack State: x86-64-desktop-drivers

## User Request
> next task from the plan — x86_64_desktop_driver_completion (6 sections: acceptance matrix, platform discovery, storage, display+input, network, verification)

## Task Type
feature

## Refined Goal
> Complete x86_64 QEMU desktop driver acceptance: define mandatory driver matrix (UEFI/ACPI/PCI/NVMe/VirtIO-BLK/framebuffer/BGA/VirtIO-GPU/PS/2/virtio-net), add boot capability summary, PCI resource ownership, unified storage results, display mode reporting, network smoke contract, and verification coverage.

## Acceptance Criteria
- [ ] AC-1: Driver acceptance matrix — mandatory device list with pass/fail/fallback status per device class
- [ ] AC-2: Boot capability summary — single serial-emitted record: platform, storage, display, input, network, DMA, interrupt_mode
- [ ] AC-3: False-claim rejection — resident-launch fallback, heap-copy DMA fallback, false acceleration all fail acceptance
- [ ] AC-4: Platform discovery — UEFI/OVMF boot path, ACPI RSDP/MADT parse, PCI device count, interrupt mode logging
- [ ] AC-5: PCI resource ownership — BAR/IRQ/DMA/device-class records before driver bind
- [ ] AC-6: Storage unification — NVMe + VirtIO-BLK shared DMA descriptor, timeout/completion-error markers
- [ ] AC-7: Display mode reporting — framebuffer/bga/virtio_gpu with accelerated=true/false, PS/2 acceptance, xHCI diagnostics
- [ ] AC-8: Network contract — virtio-net init, MAC reporting, queue setup, bounded packet/TCP smoke
- [ ] AC-9: Net capability reporting — backend capabilities with RDMA/SR-IOV/packet-IO disabled unless explicit
- [ ] AC-10: Verification spec — capability summary tests + false-claim rejection tests

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-17
- [x] 2-4 — skipped (plan doc comprehensive)
- [ ] 5-implement (Engineer)
- [ ] 6-refactor (Tech Lead)
- [ ] 7-verify (QA)
- [ ] 8-ship (Release Mgr)

## Phase Outputs

### 1-dev
10 ACs across 6 plan sections. 5 parallel agents (A-E). Existing: NVMe driver (9 files), VirtIO-BLK (4 files), PCI (1 file), framebuffer/BGA/VirtIO-GPU, PS/2 input, virtio-net, boot/limine, desktop_qemu_contract.spl, desktop_driver_summary.spl.

### 5-implement
<pending>
