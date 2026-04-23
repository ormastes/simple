# Engine2D QEMU Graphics Core System Test Plan

## Focused Host Specs

- `bin/simple test test/integration/rendering/engine2d_primitives_spec.spl`
- `bin/simple test test/unit/os/compositor/engine2d_glass_spec.spl`
- `bin/simple test test/system/engine_2d_spec.spl`

## Live QEMU Specs

Run with composite mode so `@platform: composite` specs are discovered:

- `bin/simple test test/system/engine2d_in_qemu_spec.spl '--mode=remote(baremetal(x86_64))'`
- `bin/simple test test/system/engine2d_primitives_spec.spl '--mode=remote(baremetal(x86_64))'`

## Acceptance

- Kernel ELF exists for each fixture.
- QEMU starts with a QMP socket.
- Serial contains `[E2D] Engine2D verification frame painted`.
- Serial contains `[E2D-PRIM] Engine2D primitive frame painted`.
- QMP screendump decodes as PPM and has nonzero nonblack pixels.
- Primitive pixel assertions pass for red line, green diagonal, blue filled rect, yellow stroked rect, magenta filled circle, cyan stroked circle, and black background.
- Baseline compare passes, or baseline refresh is explicit through `UPDATE_BASELINE=1`.
