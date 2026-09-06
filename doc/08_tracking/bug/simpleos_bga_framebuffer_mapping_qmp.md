# SimpleOS Freestanding Engine2D Core QMP Visibility Regression

Date: 2026-05-05

## Summary

Status: RESOLVED 2026-05-27

The live WM + Simple Web + Engine2D QEMU oracle boots, reaches the render
markers, and produces a QMP PPM with full-frame nonblack output through the
checked-in freestanding `os.compositor.engine2d_baremetal_core`
implementation. The QMP path, BGA scanout, and Simple-owned Engine2D-shaped core
are confirmed working for the current x86_64 WM Simple Web QEMU lane.

The standalone Engine2D primitive live oracle is also green on this host. The
primitive fixture now uses the x86_64 baremetal wrapper's already-initialized
`serial_println` path instead of reinitializing COM1 from Simple code, so the
guest reaches `[E2D-PRIM] Engine2D primitive frame painted` and the QMP capture
can assert exact primitive pixels.

## Evidence

- Command refreshed 2026-05-27:
  `bin/simple test test/03_system/gui_entry_engine2d_wm_simple_web_spec.spl --clean --timeout 180`
- Current passing live oracle:
  - `qmp ppm dims=1024x768`
  - `nonblack=122352`
  - `probe=true`
  - `header=true`
  - `bodyA=true`
  - `bodyB=true`
- The SimpleOS system specs were refreshed for current library paths
  (`std.nogc_sync_mut.io.file_ops` and `std.nogc_sync_mut.io.dir_ops`) and the
  WM live oracle now checks the QMP PPM with a bounded Python harness so the
  full-frame verification does not depend on slow Simple-side PPM decoding.
- Primitive oracle refreshed 2026-05-27:
  `bin/simple test test/03_system/engine2d_primitives_spec.spl --clean --timeout 180`
  passes 3/3 examples, including QMP PPM capture and exact per-primitive pixel
  checks.
- Serial proves guest progress:
  - `[GUI] mmio-probe-painted`
  - `[wm-demo] wm-service-ready`
  - `[e2d-demo] freestanding-engine2d-ready`
  - `[e2d-demo] engine-core-ready`
  - `[web-demo] pixels-ready count=114400`
  - `[integrated-demo] render-ready`
  - `TEST PASSED`

## Diagnosis

Direct runtime writes to the BGA framebuffer are QMP-visible beyond row 0. The
previous first-row-only result was caused by the active drawing path, not the
QMP screendump or framebuffer mapping. The page table diagnostic also showed
`0xfd000000` mapped as a 2MB huge page, so the earlier first-page mapping theory
is obsolete.

This is no longer a QMP connection, WM Simple Web pixel production, BGA/LFB
scanout, or missing freestanding-core issue for the x86_64 WM Simple Web QEMU
lane. The core avoids the full hosted/GPU `std.gpu.engine2d` facade in baremetal
entry-closure builds and writes through the QMP-visible framebuffer fill
primitive. Its `draw_image` path coalesces same-color row spans into rectangle
fills, which keeps the Simple Web demo fast enough for the live boot oracle.

## Remaining Risk

The restored core is intentionally narrow. The verified evidence is x86_64 QEMU
WM Simple Web plus x86_64 QEMU Engine2D primitive pixels; it is not direct
hardware-board evidence, not a claim for x86/RISC-V/ARM 32-bit or 64-bit
boards, and not proof of the full hosted Engine2D facade or Chrome-compatible
browser rendering.
