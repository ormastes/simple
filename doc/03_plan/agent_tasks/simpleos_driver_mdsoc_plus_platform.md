<!-- codex-architecture -->

# Agent Tasks: SimpleOS Driver MDSOC+ Platform

Date: 2026-05-07

## Team Lanes

### Lane 1: GPU

Owner label: `driver-gpu`

Scope: `src/os/drivers/gpu/`, `src/os/drivers/virtio/virtio_gpu.spl`, `src/os/drivers/framebuffer/`, `src/os/drivers/driver_platform_contract.spl`.

Deliverable: vendor probe adapters for CUDA, AMD, Intel, Qualcomm/ARM, and RISC-V software Vulkan/RVV.

### Lane 2: Audio

Owner label: `driver-audio`

Scope: future `src/os/drivers/audio/`, `src/os/drivers/driver_platform_contract.spl`.

Deliverable: Intel HDA controller path with Realtek HDA and Cirrus Logic HDA codec readiness, DMA ring, period/timer, mixer, and CPU acceleration evidence.

### Lane 3: Input

Owner label: `driver-input`

Scope: `src/os/drivers/input/`, `src/os/drivers/usb/`.

Deliverable: PS/2 event evidence and USB HID hotplug/hidraw bridge.

### Lane 4: Exokernel

Owner label: `driver-exokernel`

Scope: `src/os/services/driver_supervisor/`, `src/os/services/pcimgr/`, `src/os/kernel/ipc/`.

Deliverable: BAR, IRQ, DMA, IOMMU, broker, and raw-device grant evidence.

### Lane 5: MDSOC

Owner label: `driver-architect`

Scope: `doc/04_architecture/simpleos_driver_mdsoc_plus_platform.md`, `doc/03_plan/sys_test/simpleos_driver_mdsoc_plus_platform.md`, `src/os/drivers/driver_platform_contract.spl`, `src/os/drivers/driver_platform_report.spl`.

Deliverable: layer visibility audit and release-gate mapping.

## Gate

Use `DriverTeamPlan` from `src/os/drivers/driver_platform_contract.spl` and `DriverPlatformReport` from `src/os/drivers/driver_platform_report.spl`.

Every lane must provide owner, executable contract, tests, docs, and reviewer. If any one is missing, the team plan reports a specific blocker and release cannot claim full driver-platform completion.

Consumers should read the aggregated report first, then drill into the individual contract only for implementation/debugging.
