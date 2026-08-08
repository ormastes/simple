# Engine2D Vulkan and Software backends diverge on the text-heavy showcase frame (1136/30000 px)

Date: 2026-07-02
Status: open
Severity: P3 (rendering-parity gap; primitive parity gates still pass)
Found by: fable review of W1c lane (G1.1)

## Summary

The engine2d CPU/Vulkan parity gates (clear/rect readback,
`check-vulkan-engine2d-readback.shs`) pass bit-exact, but the full GUI
showcase frame rendered at 200x150 via `SIMPLE_GUI_BACKEND=vulkan` differs
from the software render of the same scene in 1136 of 30000 pixels
(3408 bytes). The W1c lane report claimed bit-exactness for the showcase
frame; that is only true for the primitive parity checks.

## Evidence

- `build/gui-window-evidence/showcase_vulkan_offscreen.ppm` vs
  `build/gui-window-evidence/sw_check.ppm` — same size (90015 B), first
  divergence at byte 2434; 1136/30000 px differ.

## Suspected cause

The divergence is most likely in the glyph path:
`_gpu_draw_text_fallback` (see `TODO(G1.1 perf)` in
`src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_helpers.spl`) reads back
and re-uploads the whole framebuffer per `draw_text`, and the round-trip
byte<->pixel conversions may not be lossless, or the fallback rasterizes
glyphs differently from `SoftwareBackend.draw_text`.

## Impact on gates

- G1.1 (Vulkan renders the showcase in a real window path): unaffected —
  the gate asserts backend provenance + widget content, not CPU identity.
- G1.4 (rendering consistency): the two-run determinism leg must be checked
  per-backend; cross-backend identity cannot be asserted until this is fixed.

## Next steps

- Diff the divergent pixel regions against glyph bounding boxes to confirm
  the text path is the source.
- Fix alongside the recorded `TODO(G1.1 perf)` glyph-bbox upload work — a
  glyph-atlas path would fix both perf and parity.
