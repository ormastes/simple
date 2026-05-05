# SimpleOS Freestanding Engine2D Core QMP Visibility Regression

Date: 2026-05-05

## Summary

The live WM + Simple Web + Engine2D QEMU oracle now boots, reaches the render
markers, and produces a decoded QMP PPM with full-frame nonblack output through
the checked-in freestanding `os.compositor.engine2d_baremetal_core`
implementation. The QMP path, BGA scanout, and Simple-owned Engine2D-shaped core
are confirmed working for the current WM Simple Web lane.

## Evidence

- Command: `bin/simple test test/system/gui_entry_engine2d_wm_simple_web_spec.spl --clean`
- Current passing live oracle:
  - `qmp ppm dims=1024x768`
  - `nonblack=122352`
  - `probe=true`
  - `header=true`
  - `bodyA=true`
  - `bodyB=true`
- `bin/simple test test/system/engine2d_primitives_spec.spl --clean` passes 3
  examples, including exact QMP-captured pixels for line, rect, filled circle,
  and stroked circle primitives.
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

This is no longer a QMP connection, PPM decode, serial marker, Simple Web pixel
production, BGA/LFB scanout, or missing freestanding-core issue. The core avoids
the full hosted/GPU `std.gpu.engine2d` facade in baremetal entry-closure builds
and writes through the QMP-visible framebuffer fill primitive. Its `draw_image`
path coalesces same-color row spans into rectangle fills, which keeps the Simple
Web demo fast enough for the live boot oracle.

## Remaining Risk

The restored core is intentionally narrow. It covers the x86_64 QEMU entries'
required methods and primitive pixels, but it is not the full hosted Engine2D
facade and does not claim Chrome-compatible browser rendering.
