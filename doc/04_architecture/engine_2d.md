# Engine2D QEMU Graphics Core Architecture

## Scope

This document locks the Simple OS/QEMU graphics-core subset of Engine2D. The target is not the full game-engine roadmap; it is the x86_64 guest path that boots in QEMU, paints deterministic 2D primitives, supports WM-facing Simple Web smoke coverage, and supports QMP framebuffer capture.

## Layers

- Mandatory BGA boot entries: `examples/simple_os/arch/x86_64/gui_entry_engine2d_min.spl`, `gui_engine2d_primitives_entry.spl`, and `gui_entry_engine2d.spl`
- VirtIO proof entry: `examples/simple_os/arch/x86_64/gui_entry_engine2d_virtio.spl`
- Engine facade: a freestanding Engine2D-style core in `src/os/compositor/engine2d_baremetal_core.spl`
- Mandatory device path: BGA/std-vga framebuffer initialized by `bga_init_framebuffer`, then pixel writes to the framebuffer scanout
- Proof device path: VirtIO-GPU wrapper initialization and direct-framebuffer backend proof, covered separately from mandatory BGA behavior
- WM Simple Web path: `gui_entry_engine2d.spl` initializes WM service and launcher state, renders Simple Web HTML to pixels, and blits those pixels through `Engine2DBaremetalCore`
- Verification: QEMU serial markers plus QMP `screendump` PPM capture

## Locked Behavior

- The entries must call Engine2D-shaped methods: `clear`, `draw_rect_filled`, `draw_rect`, `draw_line`, `draw_circle_filled`, `draw_circle`, and `present`.
- The QEMU primitive fixture must paint deterministic ARGB colors at the coordinates asserted by `test/system/engine2d_primitives_spec.spl`.
- `gui_entry_engine2d.spl` must emit WM, Simple Web, Engine2D core, and final render markers before the bounded capture window and `TEST PASSED`.
- The named scenario `x64-wm-simple-web-check` must use the BGA/std-vga path with the desktop/browser `2G` memory profile.
- `gui_entry_engine2d_virtio.spl` proves VirtIO-GPU wrapper construction and `[gui-e2d-virtio] render-ready`; it is not the mandatory graphics-core acceptance lane.
- The guest must remain alive after the paint marker so QMP capture cannot race guest exit.
- Baselines are not silently refreshed; `UPDATE_BASELINE=1` remains the intentional refresh path.

## Current Blocker

The broad `std.gc_async_mut.gpu.engine2d.engine.Engine2D` facade pulls host/GPU backend symbols into the freestanding link when its drawing methods are called from the x86_64 entry-closure kernel. A narrow internal core is therefore used for the QEMU graphics-core and WM Simple Web lanes until the compiler/linker can keep the public facade from dragging non-baremetal backends into this target.

The same boundary applies to browser rendering in QEMU: Simple Web may produce pixels, but `browser_backend` and the hosted/full `Engine2D` facade stay out of the freestanding QEMU entry closure.
