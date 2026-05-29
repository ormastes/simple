# Engine2D draw_text_bg Dispatch Gap

Date: 2026-05-05
Status: resolved 2026-05-05

## Summary

`Engine2D.draw_text_bg()` previously did not satisfy
`test/unit/lib/gc_async_mut/gpu/engine2d/draw_text_bg_spec.spl`: pixels stayed at
the clear color after calling the facade method even though `CpuBackend` had a
direct `Engine2DExtended.draw_text_bg` implementation.

The gap was caused by two issues:

- The facade fell back to `draw_rect_filled()` plus `draw_text()` instead of
  dispatching to the backend extension.
- CPU helper functions accepted `CpuBackend` by value, so helper writes mutated
  a copy rather than the stored framebuffer.

## Evidence

Command:

```bash
bin/simple test test/unit/lib/gc_async_mut/gpu/engine2d/draw_text_bg_spec.spl --clean
```

Original observed result:

- `paints bg inside the glyph cell and preserves clear outside` fails because
  the sampled inside pixel remains `0xFF00FF00`.
- `blends glyph edge coverage between bg and fg (per-pixel AA)` fails because
  no intermediate red-channel pixel is found.
- The empty-string no-op case passes.

## Fix

`Engine2D.draw_text_bg()` now imports `Engine2DExtended` and dispatches directly
to `self.backend.draw_text_bg(...)`.

`CpuBackend.draw_rect_filled()` and `CpuBackend.draw_text_bg()` now write
directly to `self.buf`, preserving clipping and bounds checks without passing the
backend through value-copy helpers. The CPU `draw_text_bg` cell height also
covers the full requested font-size cell, while glyph coverage sampling still
produces antialiased edge pixels.

Verification:

- `bin/simple check src/lib/gc_async_mut/gpu/engine2d/backend_cpu.spl src/lib/gc_async_mut/gpu/engine2d/engine.spl test/unit/lib/gc_async_mut/gpu/engine2d/draw_text_bg_spec.spl`
- `bin/simple test test/unit/lib/gc_async_mut/gpu/engine2d/draw_text_bg_spec.spl --clean`
