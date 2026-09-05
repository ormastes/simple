# Feature: SimpleOS Cross-Host QEMU and Board-GPU 2D Parity

## Raw Request

Research macOS-, Linux-, and Windows-hosted QEMU GPU acceleration for a
SimpleOS guest, covering Metal and Vulkan paths, plus native GPU acceleration
on Arduino UNO Q, StarFive VisionFive 2, and Intel UP Squared N4200; then
produce shared architecture and execution plans and define a Simple 2D
SIMD-backed bit-exact comparison without duplicating backend/evidence stacks.

## Task Type

feature

## Refined Goal

Define one evidence-driven, implementable GPU architecture for SimpleOS across
macOS/Linux/Windows QEMU hosts and UNO Q, VisionFive 2, and UP Squared native
boards that distinguishes native APIs, translation, paravirtual transport, and
CPU SIMD fallback and proves Simple 2D output by device-origin readback with
exact bit-level comparison against one canonical CPU oracle.

## Acceptance Criteria

- AC-1: Local research traces the current SimpleOS boot, QEMU device, board HAL,
  graphics driver, Draw IR, Engine2D Metal/Vulkan, CPU SIMD, readback, and
  evidence wrapper paths without treating host-side or synthetic output as
  guest/board proof.
- AC-2: Domain research cites primary sources for QEMU macOS display devices,
  HVF, virtio-gpu/virgl/rutabaga, Venus, DRM native-context/blob resources,
  MoltenVK, ANGLE, Apple virtualization GPU support, and relevant external
  memory/synchronization constraints.
- AC-3: A capability matrix separately classifies Apple Silicon and Intel macOS,
  Linux, and Windows QEMU hosts plus UNO Q/QRB2210 Adreno, VisionFive
  2/JH7110 BXE, and UP Squared N4200/Intel Gen9 boards, distinguishing `native`,
  `translated`, `software`, `experimental`, `unsupported`, and `blocked` paths
  for Metal, Vulkan, OpenGL/GLES where relevant, and Simple 2D
  presentation/readback.
- AC-4: Requirement options include pros, cons, effort, prerequisites, and
  failure modes; the user selects both the feature path and NFR targets before
  final requirements are written.
- AC-5: The selected architecture names reusable ownership boundaries from
  `Simple 2D/DrawIrComposition` through Engine2D, target capability selection,
  guest GPU transport or native-board driver adapter, host renderer/API,
  presentation, fence, and device-origin readback, while preserving CPU SIMD
  as an oracle/fallback rather than a false GPU pass.
- AC-6: The test design uses one deterministic ARGB fixture and records exact
  dimensions, stride, channel order, alpha semantics, DPI metadata, byte
  length, source/backend identity, correlated submission/readback IDs, and
  SHA-256 for every compared artifact.
- AC-7: Bit-level comparison requires `mismatch_count=0` over normalized,
  unpremultiplied-or-explicitly-premultiplied canonical ARGB bytes; any
  tolerance, blur, color-space conversion, CPU mirror, or unavailable
  device-origin readback fails the exact-parity gate.
- AC-8: Native evidence climbs
  `device initialization -> guest negotiation -> resource allocation ->
  submission -> fence -> device-origin readback -> CPU-oracle parity` and stops
  at the first unavailable rung with an explicit `blocked` or `unsupported`
  result.
- AC-9: The plan retains unavailable macOS/QEMU capability rows with exact
  prerequisites, resume commands, retained artifacts, owner, and final
  reviewer; unavailable rows are never omitted or counted as PASS.
- AC-10: The system-test plan maps every selected `REQ-NNN` and `NFR-NNN` to a
  real assertion and a mirrored operator-quality Markdown manual, with no
  placeholder passes or boolean-wrapper assertions.
- AC-11: The current-host research may run read-only readiness and existing
  evidence checks once, but it must not claim that host Metal/Vulkan rendering
  proves SimpleOS guest GPU acceleration without guest-observed and
  device-origin evidence.
- AC-12: Final verification checks affected `doc/03_plan`, `doc/04_architecture`,
  `doc/05_design`, `doc/06_spec`, `doc/07_guide`, `doc/09_report`, SPipe state,
  skills/agent/command instructions, and the generated-spec layout guard for
  consistency before the lane can be marked complete.
- AC-13: Linux and Windows QEMU rows reuse the same
  `SimpleOsGuestGpuTransport`, evidence rungs, parity artifact, and test fixture
  as macOS; host differences are isolated behind `HostGpuAdapter`.
- AC-14: UNO Q, VisionFive 2, and UP Squared rows reuse the same Engine2D
  backend-lane and evidence schema as QEMU; board-specific kernel/userspace
  drivers, firmware, IOMMU/cache-coherency rules, display paths, and deployment
  commands stay behind `NativeBoardGpuAdapter` and board capability providers.
- AC-15: Board capability claims are verified against primary vendor,
  kernel/Mesa, and Khronos sources and corrected where marketing names,
  Vulkan-version claims, OpenCL support, or upstream-driver status are not
  supported by current evidence.

## Scope Exclusions

- Implementing a new QEMU device model, Mesa/kernel driver, MoltenVK extension,
  ANGLE backend, Apple Virtualization.framework GPU device, or board GPU driver
  in this research/design turn.
- Treating a host-native result as proof for a different host/board, cross-ISA
  TCG, screenshots, synthetic
  handles, cached reports, host-only renders, or CPU mirrors as native macOS
  SimpleOS guest-GPU proof.
- Changing files currently owned by other active sessions, including the dirty
  macOS Vulkan/Metal completion plan and live Engine2D/QEMU evidence wrappers.

## Runtime Boundary Decision

- `runtime_need`: none for this research/design turn; future adapters need
  device access but must use existing owner facades or the smallest new
  owner-module facade.
- `facade_checked`: `RenderBackend`, `Engine2DReadback`,
  `engine2d_backend_lane_plan`, `SimpleOsHostGpuSession`,
  `simpleos_host_gpu_protocol`, and existing Metal/Vulkan/virtio owners.
- `chosen_path`: `reuse-facade` for shared policy; future board-specific
  capability gaps use `add-smallest-owner-facade`.
- `rejected_shortcuts`: raw `rt_*` aliases, backend field pokes, fixture-only
  GPU receipts, CPU mirrors, screenshots/QMP as device proof, platform-specific
  Draw IR forks, duplicate renderer/font/event paths, and Linux-driver UAPI
  leakage into common Engine2D.

## Cooperative Review

- Sidecar `local_stack`: trace repository owners and current evidence contracts.
- Sidecar `qemu_transport`: research QEMU/virtio-gpu/virgl/rutabaga/Venus host
  and guest constraints from primary sources.
- Sidecar `mac_graphics`: research Metal, MoltenVK, ANGLE, Apple
  virtualization capabilities from primary sources.
- Merge owner and final normal/highest-capability reviewer: root Codex agent.
- Shared interface names:
  `SimpleOsGuestGpuTransport`, `HostGpuAdapter`, `NativeBoardGpuAdapter`,
  `TargetGpuCapabilityProvider`,
  `Engine2dParityArtifact`, `Engine2dParityReceipt`,
  `GpuCapabilityObservation`, and `GpuEvidenceRung`.
- Manual `step("...")` flow names:
  `Boot SimpleOS with the requested QEMU GPU transport`;
  `Observe guest GPU negotiation and backend selection`;
  `Render the deterministic Simple 2D parity fixture`;
  `Wait for submission and device completion`;
  `Read back device-origin ARGB bytes`;
  `Compare GPU bytes with the CPU SIMD oracle`;
  `Classify unavailable host capabilities without promoting them`.
- Additional manual board step:
  `Boot the selected physical board and identify its native GPU stack`.
- Setup/checker helper names:
  `setup_simpleos_macos_qemu_gpu_fixture`,
  `check_guest_gpu_negotiation`,
  `check_device_origin_readback`,
  `check_engine2d_argb_metadata`,
  `check_exact_argb_parity`,
  `check_unavailable_gpu_row`.
- Any temporary SSpec helper must call `fail("not implemented: <helper>")`
  until it has real evidence and assertions.
- Generated-manual review owner: root Codex agent; final done marks require the
  normal/highest-capability review after sidecar findings are merged.

## Phase

design-current-host-scope-complete; external execution rows active

## Log

- dev: Created and expanded the state file to 15 acceptance criteria (type:
  feature).
- research: Extended canonical local/domain research with QEMU host and
  UNO Q/VisionFive 2/UP Squared capability corrections from primary sources.
- requirements: Added the explicitly requested shared cross-host/native-board
  extension and exact-parity/NFR requirements.
- design: Extended the canonical architecture, detail design, system-test plan,
  guide, TLDR, tracking requests, and postponement/resume matrix without
  changing Simple 2D source interfaces.
- cooperative review: local-stack, QEMU transport, and macOS graphics sidecars
  completed; primary reviewer reconciled their findings and corrected the
  Zink, Cocoa GL, Venus host, and VisionFive 2 upstream-support claims.
- status: Linux, Windows, UNO Q, VisionFive 2, and UP Squared native execution
  remain active `blocked`/`postponed` rows; the umbrella feature is not done.
- verification: `git diff --check`, SPipe command routing, both direct
  env/runtime guards, artifact-link checks, and feature-database lint passed;
  the generated-spec layout guard reported `0`. The lint command resolved to a
  bootstrap-seed binary and emitted unrelated repository diagnostics before
  its final `Lint passed: all files clean`, so no runtime/GPU evidence is
  attributed to it.
