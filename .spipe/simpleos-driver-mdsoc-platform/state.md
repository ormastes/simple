# SStack State: simpleos-driver-mdsoc-platform

## User Request
> next task from the plan — simpleos_driver_mdsoc_plus_platform (5 lanes: GPU, Audio, Input, Exokernel, MDSOC)

## Task Type
feature

## Refined Goal
> Implement the SimpleOS driver MDSOC+ platform: GPU vendor probe adapters (CUDA/AMD/Intel/Qualcomm/RISC-V), Intel HDA audio controller with codec readiness, PS/2 event evidence + USB HID hotplug bridge, exokernel resource grants (BAR/IRQ/DMA/IOMMU/broker), and MDSOC layer visibility audit with release-gate mapping.

## Acceptance Criteria
- [ ] AC-1: GPU vendor probe adapters — CUDA, AMD, Intel, Qualcomm/ARM, RISC-V software Vulkan/RVV probe contracts with typed availability results
- [ ] AC-2: GPU probe integration — adapters registered in driver_platform_contract.spl, existing virtio_gpu/framebuffer/BGA paths preserved
- [ ] AC-3: Intel HDA audio controller — HDA controller path with DMA ring buffer, period/timer, mixer volume/mute, CPU acceleration evidence fields
- [ ] AC-4: HDA codec readiness — Realtek HDA and Cirrus Logic HDA codec probe stubs with capability matrices
- [ ] AC-5: PS/2 event evidence — keyboard/mouse event structs with scan code, press/release, delta-x/y, button state, timestamp
- [ ] AC-6: USB HID hotplug bridge — HID report descriptor parser stub, hotplug/unplug detection, hidraw event forwarding
- [ ] AC-7: Exokernel BAR/IRQ/DMA grants — typed resource grant requests with capability tokens, IOMMU domain isolation
- [ ] AC-8: Exokernel broker + raw-device grant — driver_supervisor broker dispatches grants, raw-device passthrough for userspace drivers
- [ ] AC-9: MDSOC layer visibility audit — layer boundary report (kernel/service/driver/app) with import violations flagged
- [ ] AC-10: Release-gate mapping — DriverTeamPlan + DriverPlatformReport aggregation with per-lane owner/contract/tests/docs/reviewer status

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-17
- [ ] 2-4 — skipped (plan doc comprehensive)
- [ ] 5-implement (Engineer)
- [ ] 6-refactor (Tech Lead)
- [ ] 7-verify (QA)
- [ ] 8-ship (Release Mgr)

## Phase Outputs

### 1-dev
10 ACs across 5 lanes. 5 parallel agents (A-E), one per lane. Plan at doc/03_plan/agent_tasks/simpleos_driver_mdsoc_plus_platform.md. Existing infra: driver_platform_contract.spl (303 lines), driver_platform_report.spl (76 lines), virtio_gpu/framebuffer/BGA GPU drivers, PS/2 keyboard+mouse, xHCI USB, pcimgr, driver_supervisor.

### 5-implement
<pending>
