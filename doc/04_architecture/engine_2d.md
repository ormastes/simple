# Engine2D QEMU Graphics Core Architecture

## Scope

This document locks the Simple OS/QEMU graphics-core subset of Engine2D. The target is not the full game-engine roadmap; it is the x86_64 guest path that boots in QEMU, paints deterministic 2D primitives, and supports QMP framebuffer capture.

## Layers

- Boot entry: `examples/simple_os/arch/x86_64/gui_entry_engine2d_min.spl` and `gui_engine2d_primitives_entry.spl`
- Engine facade: a freestanding Engine2D-style core in `src/os/compositor/engine2d_baremetal_core.spl`
- Device path: BGA framebuffer initialized by `bga_init_framebuffer`, then pixel writes to the framebuffer scanout
- Verification: QEMU serial markers plus QMP `screendump` PPM capture

## Locked Behavior

- The entries must call Engine2D-shaped methods: `clear`, `draw_rect_filled`, `draw_rect`, `draw_line`, `draw_circle_filled`, `draw_circle`, and `present`.
- The QEMU primitive fixture must paint deterministic ARGB colors at the coordinates asserted by `test/system/engine2d_primitives_spec.spl`.
- The guest must remain alive after the paint marker so QMP capture cannot race guest exit.
- Baselines are not silently refreshed; `UPDATE_BASELINE=1` remains the intentional refresh path.

## Current Blocker

The broad `std.gc_async_mut.gpu.engine2d.engine.Engine2D` facade pulls host/GPU backend symbols into the freestanding link when its drawing methods are called from the x86_64 entry-closure kernel. A narrow internal core is therefore used for the QEMU graphics-core lane until the compiler/linker can keep the public facade from dragging non-baremetal backends into this target.
