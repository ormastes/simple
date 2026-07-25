# SStack State: dma-file-vga-driver-remaining

## Status: CLOSED — 2026-05-20

## User Request
> next task from the plan — dma_file_vga_driver_remaining (P0 DMA safety, P1 file direct I/O + display accel, P2 failure modes)

## Task Type
feature

## Refined Goal
> Implement shared DMA descriptor with cache/sync helpers, SR-IOV isolation gating, file/block direct I/O extension, display capability naming and dirty-rect flush, VirtIO-GPU DMA migration, and failure-mode safety gates.

## Acceptance Criteria
- [x] AC-1: Canonical DMA descriptor — vaddr, paddr, device_addr, byte_length, cache_policy, owner_task, owner_device with release validation
- [x] AC-2: Cache policy + sync helpers — coherent/uncached/write-combining/flush-required + CPU-to-device/device-to-CPU sync
- [x] AC-3: DMA + SR-IOV isolation gating — isolation domain records, VF fails without IOMMU, no-IOMMU doesn't advertise isolated
- [x] AC-4: Direct I/O file driver extension — explicit direct I/O capability, DMA buffer requirement, buffered default
- [x] AC-5: Block backend DMA wiring — NVMe + VirtIO-BLK submit DMA commands, timeout/completion error propagation
- [x] AC-6: Display capability naming — framebuffer-mmio/bga-write-combining/virtio-gpu-dma distinction, no false acceleration
- [x] AC-7: Dirty rectangle flushing — damaged rectangle marking, bounded flush, full-frame fallback
- [x] AC-8: VirtIO-GPU shared DMA — resource attach/transfer/flush use canonical DMA descriptor
- [x] AC-9: Failure mode safety gates — wrong-owner free, cross-device reject, SR-IOV without isolation, display DMA fallback
- [x] AC-10: Verification spec — 20 tests covering DMA, isolation, direct I/O, display, failure modes

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-18
- [x] 2-4 — skipped (plan doc comprehensive)
- [x] 5-implement (Engineer) — 2026-05-18
- [x] 6-refactor (Tech Lead) — 2026-05-18
- [x] 7-verify (QA) — 2026-05-18
- [x] 8-ship (Release Mgr) — 2026-05-18

## Phase Outputs

### 1-dev
10 ACs across P0/P1/P2. 5 parallel agents (A-E). Existing: device.spl (DmaAllocResult, SharedDmaBuffer), syscall.spl, task_cleanup.spl, nvme/, virtio_blk.spl, framebuffer/, virtio_gpu.spl, vmm.spl.

### 5-implement
5 parallel Sonnet agents. 5 files created:
- src/os/drivers/dma/dma_descriptor.spl — CachePolicy + DmaDescriptor + DmaSyncHelper + IsolationDomain + DmaRegistry
- src/os/drivers/dma/direct_io.spl — DirectIoCapability + DirectIoRequest + DirectIoResult + BlockDmaSubmit + BlockDmaCompletion
- src/os/drivers/dma/display_dma.spl — DisplayCapability + DirtyRect + DirtyRectQueue + VirtioGpuDmaTransfer + DisplayDmaManager
- src/os/drivers/dma/dma_safety_gate.spl — DmaOwnerCheck + CrossDeviceGuard + SriovIsolationGate + DisplayDmaFallbackGate + SafetyGateReport
- test/01_unit/os/dma_driver_spec.spl — 20 tests

### 7-verify
20/20 tests PASS. Commit 9cdf11de0f pushed to origin/main.
