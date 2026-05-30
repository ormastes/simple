# Engine2D QEMU Graphics Core System Test Plan

## Scope

This plan covers the QEMU/freestanding Engine2D graphics-core lane plus WM-facing Simple Web smoke coverage. It is intentionally narrower than the full game-engine roadmap: acceptance is deterministic framebuffer rendering in x86_64 QEMU, serial markers, and QMP screendump evidence.

## Focused Host Specs

- `bin/simple test test/integration/rendering/engine2d_backend_spec.spl`
- `bin/simple test test/integration/rendering/engine2d_primitives_spec.spl`
- `bin/simple test test/unit/os/compositor/engine2d_glass_spec.spl`
- `bin/simple test test/system/engine_2d_spec.spl`

## Live QEMU Specs

Run the live QEMU specs:

- `bin/simple test test/system/engine2d_in_qemu_spec.spl '--mode=remote(baremetal(x86_64))'`
- `bin/simple test test/system/engine2d_primitives_spec.spl '--mode=remote(baremetal(x86_64))'`
- `bin/simple test test/system/gui_entry_engine2d_virtio_spec.spl '--mode=remote(baremetal(x86_64))'`
- `bin/simple test test/system/gui_entry_engine2d_wm_simple_web_spec.spl`

The BGA/std-vga path is mandatory coverage for Engine2D graphics-core and WM-facing Simple Web acceptance. The VirtIO-GPU entry is wrapper proof coverage only and does not replace the BGA lane.

## Named Scenario Acceptance

- `bin/simple os build --scenario=x64-wm-simple-web-check`
- `bin/simple os test --scenario=x64-wm-simple-web-check`

The named scenario binds to `examples/simple_os/arch/x86_64/gui_entry_engine2d.spl`, uses the proven desktop/browser `2G` memory profile, and keeps full QMP/framebuffer capture plus serial-marker validation in `test/system/gui_entry_engine2d_wm_simple_web_spec.spl`.

## Acceptance

- Kernel ELF exists for each fixture.
- QEMU starts with a QMP socket.
- Serial contains `[E2D] Engine2D verification frame painted`.
- Serial contains `[E2D-PRIM] Engine2D primitive frame painted`.
- Serial contains `[wm-demo] wm-service-ready`.
- Serial contains `[e2d-demo] engine-core-ready`.
- Serial contains `[web-demo] pixels-ready`.
- Serial contains `[integrated-demo] render-ready`.
- Serial contains `[gui-e2d-virtio] render-ready` for the VirtIO wrapper proof lane.
- QMP screendump decodes as PPM and has nonzero nonblack pixels.
- Primitive pixel assertions pass for red line, green diagonal, blue filled rect, yellow stroked rect, magenta filled circle, cyan stroked circle, and black background.
- Baseline compare passes, or baseline refresh is explicit through `UPDATE_BASELINE=1`.

## Traceability

| Requirement | Evidence |
|-------------|----------|
| `REQ-ENG-003` Engine2D backend lifecycle/discovery works on host | `test/integration/rendering/engine2d_backend_spec.spl` |
| `REQ-ENG-008` Engine2D primitives draw deterministic pixels | Host primitive spec plus `test/system/engine2d_primitives_spec.spl` |
| `NFR-E2D-QEMU-001` BGA/std-vga QEMU lane is mandatory | `engine2d_in_qemu_spec.spl`, `engine2d_primitives_spec.spl`, `gui_entry_engine2d_wm_simple_web_spec.spl` |
| `NFR-E2D-QEMU-002` VirtIO remains proof coverage | `gui_entry_engine2d_virtio_spec.spl` |
| `NFR-E2D-QEMU-003` No silent baseline refresh | `UPDATE_BASELINE=1` gate in `engine2d_in_qemu_spec.spl` |
| `NFR-E2D-QEMU-004` QMP capture validates rendered pixels | QMP PPM assertions in all live graphics specs |
| `NFR-E2D-QEMU-005` Freestanding closure avoids hosted/GPU backend leakage | `gui_entry_engine2d.spl` uses `Engine2DBaremetalCore` and Simple Web pixels, not `browser_backend` or full hosted `Engine2D` |
| `NFR-E2D-QEMU-006` Scenario memory matches desktop/browser needs | `x64-wm-simple-web-check` uses `2G`, not low-memory probe settings |
| WM architecture coverage | `gui_entry_engine2d_wm_simple_web_spec.spl` verifies WM service, launcher, Simple Web pixel production, Engine2D blit, and final render marker |
