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
- [x] 5-implement (Engineer) — 2026-05-17
- [x] 6-refactor (Tech Lead) — 2026-05-17
- [x] 7-verify (QA) — 2026-05-17
- [x] 8-ship (Release Mgr) — 2026-05-17

## Phase Outputs

### 1-dev
10 ACs across 5 lanes. 5 parallel agents (A-E), one per lane. Plan at doc/03_plan/agent_tasks/simpleos_driver_mdsoc_plus_platform.md. Existing infra: driver_platform_contract.spl (303 lines), driver_platform_report.spl (76 lines), virtio_gpu/framebuffer/BGA GPU drivers, PS/2 keyboard+mouse, xHCI USB, pcimgr, driver_supervisor.

### 5-implement
5 parallel Sonnet agents. 11 files created:
- src/os/drivers/gpu/gpu_vendor_probe.spl (296 lines) — 5 vendor probe classes + registry
- src/os/drivers/gpu/gpu_vendor_integration.spl (131 lines) — platform bridge + lane status
- src/os/drivers/audio/hda_controller.spl (284 lines) — HDA ring buffer, timer, mixer, controller
- src/os/drivers/audio/hda_codec_probe.spl (179 lines) — Realtek/Cirrus codec + lane status
- src/os/drivers/input/input_event.spl (233 lines) — Key/Mouse/Touch/Gamepad events + queue
- src/os/drivers/usb/usb_hid_bridge.spl (271 lines) — HID descriptor, device, hotplug bridge
- src/os/services/driver_supervisor/resource_grant.spl — BAR/IRQ/DMA/IOMMU grants
- src/os/services/driver_supervisor/grant_broker.spl — broker + raw-device passthrough
- src/os/drivers/driver_layer_audit.spl (205 lines) — MDSOC layer visibility audit
- src/os/drivers/driver_release_gate.spl (220 lines) — DriverTeamPlan + DriverPlatformReport
- test/unit/os/driver_platform_spec.spl — 18 tests
### 7-verify
18/18 tests PASS. Commit b97a81b1fc pushed to origin/main.
