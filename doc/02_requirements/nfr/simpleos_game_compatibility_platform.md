<!-- codex-architecture -->

# NFR Requirements: SimpleOS Game Compatibility Platform

Date: 2026-05-07

## NFR-GAME-001: Truthful Compatibility Claims

No target may be marked `ready` or `verified` from a stub, resident fallback, hidden host dependency, or unchecked marker string.

Acceptance:

- Each readiness marker has a unit or integration test.
- Missing Linux ABI, Vulkan, audio, input, filesystem, or network capabilities produce structured blockers.

## NFR-GAME-002: Latency Budget

Game foreground scheduling must preserve frame, audio, and input latency.

Acceptance:

- Game foreground, audio realtime, render critical, and I/O streaming scheduling classes are documented before implementation.
- Audio period and frame pacing evidence are required for runtime readiness.

## NFR-GAME-003: Sandboxing

Game launch must be capability scoped.

Acceptance:

- Per-game filesystem, network, IPC, process, and device policies are explicit.
- Raw device access requires IOMMU or a brokered capability boundary.

## NFR-GAME-004: Portability

x86_64 is first, but architecture records must not block ARM or RISC-V lanes.

Acceptance:

- CPU fallback probes cover x86 SIMD, ARM NEON/SVE, and RISC-V RVV.
- Non-x86 Proton targets are blocked on a named CPU translation layer, not silently rejected.

## NFR-GAME-005: Developer Diagnostics

Failures must be actionable.

Acceptance:

- Porting toolkit reports identify missing syscall, ioctl, library, codec, shader, device, or runtime feature.
- Reports must include path, target, observed state, and next missing gate.
