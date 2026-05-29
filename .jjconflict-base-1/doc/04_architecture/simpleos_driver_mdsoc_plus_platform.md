<!-- codex-architecture -->

# Architecture: SimpleOS Driver MDSOC+ Platform

Date: 2026-05-07

## Decision

Make driver support concrete through evidence contracts first, then hardware-specific services. The platform target is GPU, audio, keyboard, mouse, and exokernel device access with MDSOC+ separation between common readiness records, vendor probes, hardware services, and team execution lanes.

The executable anchors are `src/os/drivers/driver_platform_contract.spl` and
`src/os/drivers/driver_platform_report.spl`.

## Layers

### Layer 1: Driver Evidence Contracts

Paths:

- `src/os/drivers/driver_platform_contract.spl`
- `src/os/drivers/driver_platform_report.spl`

Owns GPU vendor probes, CPU fallback kernels, Intel HDA plus Realtek/Cirrus codec probes, PS/2 and USB HID input probes, exokernel grants, team readiness lanes, and the aggregated consumer-facing readiness report.

### Layer 2: Hardware Discovery And Brokering

Paths: `src/os/services/pcimgr/`, `src/os/services/driver_supervisor/`.

Owns PCI/device matching, driver process lifecycle, and capability brokering. It must consume readiness records instead of trusting vendor strings.

### Layer 3: Device Families

Paths: `src/os/drivers/gpu/`, future `src/os/drivers/audio/`, `src/os/drivers/input/`, `src/os/drivers/usb/`.

Owns hardware-specific implementation after the contract says what evidence is required.

### Layer 4: Consumers

Paths: `src/os/drivers/desktop_driver_summary.spl`, `src/os/game/platform/compatibility_contract.spl`.

Consumers depend on `driver_platform_report_marker`, typed blockers, and readiness probes, not private driver internals.

## MDSOC Visibility Matrix

| Raw layer | Common node | Public to parent | Public to next-layer sibling |
| --- | --- | --- | --- |
| `src/os/drivers/gpu/` | `driver_platform_contract.spl` | vendor/runtime/device/queue/memory status | marker and blocker only |
| `src/os/drivers/audio/` | `driver_platform_contract.spl` | controller/codec/DMA/period/mixer/CPU accel status | codec readiness only |
| `src/os/drivers/input/` | `driver_platform_contract.spl` | keyboard/mouse/events/hotplug/hidraw status | input readiness only |
| `src/os/services/driver_supervisor/` | `driver_platform_contract.spl` | BAR/IRQ/DMA/IOMMU/broker/raw-device safety | brokered grants only |
| team execution lanes | `driver_platform_contract.spl` | owner/contract/tests/docs/reviewer status | release verifier reads blockers |
| desktop/game/release consumers | `driver_platform_report.spl` | first blocker and summary marker | no direct vendor/device internals |

## Rules

- Framebuffer, BGA, and VirtIO-GPU cannot claim GPU compute without runtime/device/queue/memory evidence.
- Raw app device access requires IOMMU; otherwise use a brokered exokernel grant.
- Audio readiness requires controller, codec, DMA ring, period/timer, mixer, and non-scalar CPU audio acceleration.
- USB HID input is partial until hotplug and hidraw are both present.
- Team infra is not ready until every lane has owner, contract, tests, docs, and reviewer evidence.
- Release consumers must use `DriverPlatformReport` so the first concrete blocker is visible.

## Migration Sequence

1. Keep `driver_platform_contract.spl` as the common readiness node.
2. Add `src/os/drivers/audio/` HDA implementation and bind it to Realtek/Cirrus probes.
3. Extend USB HID input from `src/os/drivers/usb/` into `src/os/drivers/input/`.
4. Add GPU family service adapters that populate the vendor probe records.
5. Wire driver supervisor grants to `ExokernelDeviceGrant`.
6. Use `DriverPlatformReport` and `DriverTeamPlan` before claiming complete driver-platform support.
