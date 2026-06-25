<!-- codex-architecture -->

# System Test Plan: SimpleOS Driver MDSOC+ Platform

Date: 2026-05-07

## Automated Gate

- `/home/ormastes/dev/pub/simple/bin/simple check src/os/drivers/driver_platform_contract.spl src/os/drivers/desktop_driver_summary.spl src/os/drivers/mod.spl`
- `/home/ormastes/dev/pub/simple/bin/simple test test/01_unit/os/drivers/driver_platform_contract_spec.spl --mode=interpreter`
- `/home/ormastes/dev/pub/simple/bin/simple test test/01_unit/os/drivers/driver_platform_report_spec.spl --mode=interpreter`
- `/home/ormastes/dev/pub/simple/bin/simple test test/01_unit/os/qemu_runner_spec.spl --mode=interpreter`

## Coverage

### ST-DRV-001: GPU Vendor Probe Matrix

NVIDIA CUDA, AMD, Intel, Qualcomm/ARM, and RISC-V software Vulkan/RVV probes must report exact missing runtime/device/queue/memory blockers. Framebuffer, BGA, and VirtIO-GPU must reject compute false claims.

### ST-DRV-002: CPU Fallback

x86 MMX/SSE2/SSE4/AVX2, ARM NEON/SVE, RISC-V RVV, and scalar fallback must be selected deterministically. Scalar audio cannot satisfy accelerated audio readiness.

### ST-DRV-003: Audio Brands

Intel HDA with Realtek HDA and Cirrus Logic HDA codec lanes must require controller, codec, DMA ring, period, mixer, and CPU acceleration evidence.

### ST-DRV-004: Keyboard And Mouse

PS/2 keyboard/mouse must require event delivery. USB HID must remain partial until hotplug and hidraw are present.

### ST-DRV-005: Exokernel Device Grant

BAR, IRQ, DMA, IOMMU, broker, and raw app-device states must be represented. Raw app-device access without IOMMU must report unsafe.

### ST-DRV-006: Team Infra

GPU, audio, input, exokernel, and MDSOC lanes each require owner, contract, tests, docs, and reviewer evidence.

### ST-DRV-007: Aggregated Report

`DriverPlatformReport` must report the first concrete blocker across GPU, CPU pixel/audio fallback, primary/secondary audio codecs, keyboard/mouse input, exokernel grant safety, and team lanes. The report marker is the consumer-facing release gate.

## Exit Criteria

All tests pass, and no consumer doc or marker claims broader hardware support than the executable probe covers.
