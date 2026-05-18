# SStack State: dma-file-vga-driver-remaining

## User Request
> next task from the plan — dma_file_vga_driver_remaining (P0 DMA safety, P1 file direct I/O + display accel, P2 failure modes)

## Task Type
feature

## Refined Goal
> Implement shared DMA descriptor with cache/sync helpers, SR-IOV isolation gating, file/block direct I/O extension, display capability naming and dirty-rect flush, VirtIO-GPU DMA migration, and failure-mode safety gates.

## Acceptance Criteria
- [ ] AC-1: Canonical DMA descriptor — vaddr, paddr, device_addr, byte_length, cache_policy, owner_task, owner_device with release validation
- [ ] AC-2: Cache policy + sync helpers — coherent/uncached/write-combining/flush-required + CPU-to-device/device-to-CPU sync
- [ ] AC-3: DMA + SR-IOV isolation gating — isolation domain records, VF fails without IOMMU, no-IOMMU doesn't advertise isolated
- [ ] AC-4: Direct I/O file driver extension — explicit direct I/O capability, DMA buffer requirement, buffered default
- [ ] AC-5: Block backend DMA wiring — NVMe + VirtIO-BLK submit DMA commands, timeout/completion error propagation
- [ ] AC-6: Display capability naming — framebuffer-mmio/bga-write-combining/virtio-gpu-dma distinction, no false acceleration
- [ ] AC-7: Dirty rectangle flushing — damaged rectangle marking, bounded flush, full-frame fallback
- [ ] AC-8: VirtIO-GPU shared DMA — resource attach/transfer/flush use canonical DMA descriptor
- [ ] AC-9: Failure mode safety gates — wrong-owner free, cross-device reject, SR-IOV without isolation, display DMA fallback
- [ ] AC-10: Verification spec — 20 tests covering DMA, isolation, direct I/O, display, failure modes

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-18
- [x] 2-4 — skipped (plan doc comprehensive)
- [ ] 5-implement (Engineer)
- [ ] 6-refactor (Tech Lead)
- [ ] 7-verify (QA)
- [ ] 8-ship (Release Mgr)

## Phase Outputs

### 1-dev
10 ACs across P0/P1/P2. 5 parallel agents (A-E). Existing: device.spl (DmaAllocResult, SharedDmaBuffer), syscall.spl, task_cleanup.spl, nvme/, virtio_blk.spl, framebuffer/, virtio_gpu.spl, vmm.spl.

### 5-implement
<pending>
