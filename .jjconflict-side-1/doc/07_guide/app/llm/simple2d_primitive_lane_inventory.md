# Simple 2D Primitive Lane Inventory

Use this page when a task mentions buttons, window dragging, CSS/layout,
scrolling, fonts, Simple 2D, WM, GUI, Web, or SimpleOS/QEMU rendering.

## Canonical reading order

1. Architecture: `doc/04_architecture/simple2d_primitive_lane.md`
2. Detail design: `doc/05_design/simple2d_primitive_lane.md`
3. Test plan: `doc/03_plan/sys_test/simple2d_primitive_lane.md`
4. QEMU/GPU contract: `doc/04_architecture/simpleos_qemu_host_gpu_2d.md`,
   `doc/05_design/simpleos_qemu_host_gpu_2d.md`, and
   `doc/03_plan/sys_test/simpleos_qemu_host_gpu_2d.md`
5. SPipe guidance: `.codex/skills/system_test/SKILL.md` and
   `doc/00_llm_process/llm_wiki.md` (spec verdict/evidence rules).

## Routing table

| Request | Start with | Evidence owner |
|---|---|---|
| Web/CSS/layout | browser renderer and layout tests | Web semantic/layout owner |
| GUI button/key/focus | widget and GUI event pipeline | GUI event owner |
| WM drag/scroll | WM action, capture, and layout owners | WM compositor owner |
| 2D drawing/animation/font | `DrawIrComposition`, Engine2D, showcase | 2D executor owner |
| SimpleOS/QEMU | canonical host-GPU wrapper and receipt parser | QEMU transport owner |

## Non-negotiable evidence

The host may establish semantic correctness, but it does not prove a QEMU GPU
row. Vulkan promotion requires selected Vulkan, fenced device execution,
device-origin readback, positive identity/handle, exact CPU parity, and complete
font evidence. Twenty warm samples, nearest-rank p95, and combined RSS are
required for the performance row. TCG, screenshots, QEMU flags, CPU mirrors,
source checks, and phase-2 diagnostics retain their narrower classification.

## Agent handoff

Use small disjoint sidecars for Web/CSS, GUI button/key, WM drag/scroll, and
2D/font/Vulkan/QEMU. Sidecars report paths, reproducer, requirement, and
evidence class. `/root` merges and owns the final verification; Sol reviews
architecture, SPipe manuals, and performance claims. Never create a parallel
renderer, event router, font atlas, or host-specific primitive API.
