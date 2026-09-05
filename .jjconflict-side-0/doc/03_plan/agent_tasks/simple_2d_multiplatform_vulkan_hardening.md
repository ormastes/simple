<!-- codex-design -->
# Simple 2D Multiplatform Vulkan Hardening — Interface-First Agent Plan

Scope: contracts, implementation, and evidence for Linux, ARM64 SimpleOS/QEMU,
macOS preparation, and UNO Q. The shared names below are frozen before any
parallel implementation. Merge owner: `/root`. Final reviewer: normal/highest
capability reviewer. Lower-model sidecars: N/A until the compiler dispatch
repair establishes a runnable native boundary; after that, bounded inventory
work only may use Codex Luna/Claude Haiku.

## Shared interfaces and helper names

| Item | Frozen name |
|---|---|
| Common facade | `GpuAccelerationProvider`, `GpuProviderCapabilityReceipt`, `GpuExecutionReceipt` |
| Transport facade | `VirtioGpuDiscoveryProvider`, `VirtioGpuDiscoveryReceipt` |
| Venus progression | `VenusProtocolProbe`, `VenusSession`, `VenusCommandQueue`, `VenusFenceReceipt`, `VenusDeviceReadbackReceipt` |
| Runtime ownership | `VulkanRuntimeLifecycle`, `VulkanSession.runtime_lease_held` |
| ARM join | `Arm64WmIoReceiptOwner`, `Arm64WmIoFrameReceipt` |
| Showcase/manual steps | `confirm_cached_hello_admission`, `submit_fenced_drawir_frame`, `publish_arm64_io_frame_receipt`, `capture_animated_font_showcase`, `measure_warm_qemu_vulkan_profile` |
| Fail-fast placeholders | `fail("device DrawIR execution evidence missing")`, `fail("ARM IO/frame receipt missing")` |

## Non-overlapping lanes

| Lane | Owner scope | Deliverable and stop condition |
|---|---|---|
| 1. Native dispatch/replay | compiler + QEMU owner | Fresh compile of the nominal dispatch repair; one bounded post-HELLO request produces either actionable failure evidence or a correlated device receipt. Do not alter UI semantics. |
| 2. Common/Venus | GPU transport owner | Implement common projection then private protocol/queue/fence/readback in dependency order. Stop at a rejected/unproven stage; do not enable compositor early. |
| 3. ARM IO/showcase | ARM WM/audio owner | Implement atomic coordinator using existing input/audio/WM owners; prove event/audio-to-frame correlation, then request the same DrawIR capture. |
| 4. Host/profile evidence | Linux/macOS/board owner | Linux device run and profile receipt; macOS test/preparation matrix; UNO Q attached-runner acquisition and fail-closed rows. No borrowed host evidence. |

No lane may add a renderer, image/atlas cache, input parser, audio driver,
receipt schema, or backend selection policy parallel to the frozen owners.
Any required interface change updates architecture and detail design first.

## Ordered dependencies

1. Lane 1 unblocks the first QEMU render replay. Its current blocker is native
   nominal dispatch, after physical Vulkan HELLO; it must retain daemon
   termination and request/completion generation evidence even on failure.
2. Lane 2 discovery is already bounded, but its current state is not execution.
   Protocol -> blob/ring -> queue -> fence -> readback is the only promotion
   order. `VenusDiscovered` cannot enable a compositor.
3. Lane 3 can prepare/coordinator-test independently, but live frame proof
   waits for Lane 1/2 execution. Reuse both Ctrl and Alt mappings, pointer,
   wheel, and VirtIO-SND completion owners.
4. Lane 4 may publish only profile-qualified results. Linux needs device
   execution; macOS needs a macOS host; UNO Q needs an attached board.

## Evidence gates

| Gate | Required fields | Reject examples |
|---|---|---|
| HELLO | bounded version/masks/physical admission and generation | claiming handle, pixels, or render PASS |
| Device frame | generation/run/frame tuple, Vulkan, fence, positive handle/identity, device readback, checksum, coverage, CPU parity | cache/scanout/CPU source, skipped command, stale tuple |
| ARM IO frame | ordered input/modifiers, WM action/epoch, frame tuple, audio completion where requested | separately parsed receipts, stale capture, cross-session join |
| Showcase | animated distinct frames, DrawIR text/font batch, events, audio requested/completed, capture path | screenshot-only, source scan, uncorrelated audio |
| Performance | 20 warm samples, nearest-rank p95, daemon/QEMU/combined RSS, exact executable/argv/device/profile | cold-only, TCG latency, historical/cross-host data |

## Current profile ledger

- Linux: cacheable physical Vulkan HELLO exists at `e5f8d170`; full submission
  remains unproven.
- ARM64 QEMU: boot/BAR/HELLO and source contracts are narrow progress; first
  render is blocked by native nominal dispatch. No live showcase claim.
- macOS: emulator/implementation/test work only on this host; TODO 660 remains
  fail-closed.
- UNO Q: `board-not-connected`/`runner-not-yet-implemented` remain required
  blocked outcomes until physical board evidence exists (TODO 658).

## Handoff checklist

Before merging any lane, provide changed-file list, one executed command per
acceptance criterion, profile and exact artifact paths, negative-path result,
and a statement that no parallel renderer/event/audio/font owner was added.
The final merge checks this document, the architecture/design pair, existing
QEMU/Venus/differential docs, and the generated showcase manual together.
