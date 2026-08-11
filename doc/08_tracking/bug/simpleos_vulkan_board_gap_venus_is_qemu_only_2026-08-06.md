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

Open. No fix attempted — this is a scope/architecture gap, not a bug in
existing code. Tracked pointers: `doc/03_plan/os/simpleos/screens_showcase_2d_opt_plan.md`
and `.spipe/simpleos-screens-render-lane/state.md:178` already acknowledge a
board gap in general terms; this file makes the Vulkan-specific instance
explicit per the board-runnable rule's "say so and file it" requirement.
