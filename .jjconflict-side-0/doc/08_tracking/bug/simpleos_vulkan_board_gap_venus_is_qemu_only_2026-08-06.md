# SimpleOS Vulkan backend: venus/virtio-gpu is QEMU-only, no board path

**Filed:** 2026-08-06
**Source:** lane G0, `doc/04_architecture/os/vulkan/simpleos_vulkan_render_backend_plan.md`

## Problem

The planned Vulkan render backend (`doc/04_architecture/os/vulkan/simpleos_vulkan_render_backend_plan.md`)
is built entirely on virtio-gpu + venus, which is a **VM device interface** —
it has no meaning on physical hardware. Per the repo's board-runnable rule
(`.claude/rules/board-runnable.md`), a QEMU-only render path is a defect to
flag explicitly, not a completed capability.

Board support for this backend would require an entirely separate, real GPU
driver written against actual hardware — not a continuation of the
venus/virtio-gpu work. No such driver exists, is planned, or is scoped here.

## Second, narrower gap

Even the QEMU side is currently unproven: per
`doc/01_research/os/vulkan/venus_virtio_gpu_protocol_facts.md`, `virtio-gpu-gl`
reportedly fails to load on the host that research was written against. So
neither the QEMU proxy path nor a board path is demonstrated working today.

## Status

**2026-08-10 — architecture corrected; board gap now measured, still open.**

The scope error is fixed: venus is no longer the architecture. A SoC-neutral
board Vulkan core with one thin backend per GPU now exists, and venus is one of
those backends carrying `qemu_only: true`.

- Architecture: `doc/04_architecture/os/vulkan/simpleos_board_vulkan_driver_architecture_2026-08-10.md`
- Lanes: `doc/03_plan/os/vulkan/board_vulkan_parallel_soc_lanes_2026-08-10.md`
- Code: `src/os/drivers/gpu/board_vulkan/` — `soc_profile.spl` (honesty gate),
  `backend_{virtio_venus,intel_gen12,adreno,img_bxe}.spl` (one file per parallel
  lane), `counterpart_plan.spl` (IO-compare plan descriptors against Mesa
  turnip / anv / powervr, reusing the existing counterpart framework).
- Spec: `test/01_unit/os/vulkan/board_vulkan_counterpart_plan_spec.spl`

What is still open, and why this file stays open: **no board GPU encoder is
written.** All three board backends declare `spirv/submit/readback = false`, so
`board_profile_is_board_runnable` is false for every backend and the
board-runnable count is asserted to be **0**. The gap is now a failing-if-flipped
measurement instead of prose, but it is still a gap. The narrower QEMU-side
`virtio-gpu-gl` load failure is also still open and is tracked as lane B0 stage 4.

Original tracked pointers: `doc/03_plan/os/simpleos/screens_showcase_2d_opt_plan.md`
and `.spipe/simpleos-screens-render-lane/state.md:178` already acknowledge a
board gap in general terms; this file makes the Vulkan-specific instance
explicit per the board-runnable rule's "say so and file it" requirement.
