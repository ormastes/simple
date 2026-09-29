# Bug: Engine2D fast Metal web lane always returns a 1x1 framebuffer (clip poisons GPU readback)

- **Status:** fixed (2026-07-03)
- **Component:** `src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl`
- **Discovered via:** `examples/06_io/ui/wm_fullscreen_metal_gui.spl` web-engine phase
  (`scripts/check/check-macos-wm-fullscreen-metal-evidence.shs`) — the marker
  `[wm-fullscreen] web_engine=short pixels=1 want=7339320`.

## Symptom

`simple_web_layout_render_html_pixels_engine2d(html, w, h, "metal")` (the fast
CSS/GUI web lane in
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_layout_engine2d_fast.spl`)
returned a length-1 `[u32]` for a non-trivial HTML document on a real Metal GPU,
instead of the full `w*h` framebuffer. `host_compositor_entry.render_frame()`
silently tolerated this (its `chrome_px.len() == total` guard failed, so it fell
back to direct-draw and never actually exercised the CSS lane on Metal).

## Root cause

`simple_web_layout_render_html_draw_ir()` wraps the whole document in a single
Draw IR batch whose embedding has `clip: true` covering the full surface
(`draw_ir_embedding_config(..., true)` at
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl:7579`);
`overflow:hidden` elements add further clip batches.

`engine2d_draw_ir_adv_composition()` translates each clipped batch into
`engine.set_clip(...)` / `engine.clear_clip()`. On `MetalBackend`, both of those
unconditionally set `gpu_frame_complete = false`. Two consequences:

1. Subsequent draw ops accumulate through `gpu_frame_complete = gpu_frame_complete
   and _dispatch_metal_*(...)`. With the flag already `false`, the `and`
   short-circuits and the GPU dispatch is skipped — the GPU framebuffer never
   receives the draws.
2. `read_pixels()` only downloads from the GPU when `gpu_frame_complete` is true;
   otherwise it returns `self.mirror.read_pixels()`, which in fast mode is the
   1x1 mirror (`use_gpu_only()` shrinks it).

So on Metal the fast lane always fell back to a 1x1 mirror.

## Fix

In `use_gpu_only()` (fast) mode the 1x1 CPU mirror cannot enforce a clip, and the
Metal dispatch path does not apply one either, so a clip is a no-op. `set_clip`
and `clear_clip` now skip the `gpu_frame_complete = false` reset when the backend
is in GPU-only mode (detected by `_gpu_only_mode()`: mirror is 1x1 while the GPU
framebuffer holds the full surface). The flag stays armed, every draw op
dispatches to the GPU, and `read_pixels()` downloads the real framebuffer.

Non-fast (mirror-backed) mode is unchanged: clips still fall back to the CPU
mirror for correct clipped output.

## Verification

`scripts/check/check-macos-wm-fullscreen-metal-evidence.shs` web-engine phase now
renders a 3-window WM desktop via HTML/CSS on the Metal GPU at physical fullscreen
dims and reads back the full framebuffer (`web_engine=render ... pixels=<w*h>`).
