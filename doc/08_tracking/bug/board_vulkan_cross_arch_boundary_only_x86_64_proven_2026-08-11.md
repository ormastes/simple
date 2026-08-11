# Board-Vulkan cross-arch boundary capture: only x86_64 proven (lane L6)

**Status:** Open — QEMU-only / single-arch, filed per `.claude/rules/board-runnable.md`
**Date:** 2026-08-11
**Owner:** lane L6, board-Vulkan parallel SoC lanes campaign
**Related:** `doc/03_plan/os/vulkan/board_vulkan_parallel_soc_lanes_2026-08-10.md` § "Per-architecture status (lane L6)"

## Summary

The board-Vulkan boundary comparison (SPIR-V binary / command stream /
readback image vs. an open-source counterpart) is only ever executed on the
x86_64 development host today. The other two board-Vulkan targets — Adreno
(aarch64) and IMG BXE-4-32 (riscv64) — have no verified real-firmware QEMU
boot path in this repo for this purpose:

- **aarch64**: no EDK2/AAVMF real-firmware boot record was found under
  `doc/03_plan/os/simpleos/hw_qemu/`. Only a Limine-framebuffer check
  (`scripts/check/check-simpleos-aarch64-limine-framebuffer.shs`) and a
  general ARM QEMU fs/toolchain verification doc exist — neither is an
  EDK2-AAVMF real-firmware boot record, and neither shows a Vulkan device
  path. The board-runnable rule's claim that aarch64 lacks an EFI-stub was
  not disproven by this search.
- **riscv64**: OpenSBI-related build scripts
  (`scripts/os/build_opensbi_rv64_soc.shs`) and a hosted-QEMU plan doc exist,
  but no evidence was found that the OpenSBI path has actually been run as
  the real-firmware proxy (as opposed to `-kernel` semantics) for a
  Vulkan-capable guest, and no IMG BXE-4-32 in-guest device path evidence
  was located.
- **x86_64 itself is not fully board-runnable either**: the only proven
  in-guest GPU device path is virtio-gpu/venus, which is QEMU-only per the
  existing counterpart plan (`backend_virtio_venus.spl`), not the native
  Intel Gen12 bare-metal path.

## What lane L6 built to prevent this being silently misreported

- `src/os/drivers/gpu/board_vulkan/boundary_arch.spl` — architecture-tagged
  boundary capture record (`ArchBoundaryCapture`, reusing the existing
  `environment_profile` field convention from `CounterpartPlan` /
  `ProvenanceReceipt` / `CounterpartRun` in
  `src/lib/common/spec/evidence/counterpart/model.spl`), plus:
  - `cross_arch_comparison_rejections` / `cross_arch_comparison_is_valid` —
    fail-closed rejection of a comparison between two different
    architectures' captures, unless the boundary is declared
    architecture-invariant (`boundary_is_arch_invariant` — true only for
    `vulkan.shader.spirv_binary@1`; command streams and readback images are
    architecture-specific).
  - `arch_coverage_count` / `arch_coverage_archs` — a truthful count of how
    many architectures ACTUALLY produced a captured record for a boundary,
    so a caller cannot claim "3-arch coverage" when only x86_64 executed.
- `test/01_unit/os/vulkan/cross_arch_boundary_substitution_spec.spl` — pins
  both the cross-arch rejection and the truthful coverage count, including
  sabotage proofs (see the spec run log referenced from the plan doc) that
  a fabricated aarch64-vs-x86_64 substitution is rejected, and that a false
  three-arch coverage claim is reported as 1.

## Unblock condition

Filed as a genuine blocker, not implied as done:

1. A verified EDK2/AAVMF real-firmware QEMU boot record for aarch64 SimpleOS
   (or a documented replacement per the board-runnable rule), plus an
   in-guest Adreno (or any) Vulkan device path.
2. A verified OpenSBI real-firmware (not `-kernel`) QEMU boot record for
   riscv64 SimpleOS with an in-guest IMG BXE-4-32 (or any) Vulkan device
   path.
3. A native (non-virtio) Intel Gen12 in-guest device path for x86_64, since
   the current virtio-gpu/venus path is explicitly QEMU-only.

Only once at least one real capture exists per architecture does
`arch_coverage_count` for a given boundary legitimately reach more than 1 —
until then, any report of multi-architecture board-Vulkan coverage is false
and this record documents why.
