# Interpreter: CompositorBackend.put_pixel clones the whole framebuffer per pixel

- id: interp_compositor_backend_put_pixel_clones_framebuffer_2026-07-03
- status: worked around in the compositor (interpreter root cause still open)
- workaround (2026-07-04): `HeadlessHostCompositorBackend.fill_rect` and
  `.blit_pixels` now write `self.pixels` inline in their own loops with
  once-up-front clamping (no per-pixel `me`->`me` delegation). Measured:
  fill_rect 300x200 went from never-finishing-in-120s to 333ms; the
  host_compositor gate scene went from >1800s timeout to 23.5s with real
  content. Single-shot `me`->`me` calls (draw_text -> fill_rect once per
  call) remain acceptable (one object clone per call, not per pixel).
  Also fixed while here: the evidence driver read the LOCAL `backend`
  binding after `comp.render_frame()` — mutations through `comp.backend` do
  not reflect into the local binding (value-semantics write-back), so it
  captured an all-zero buffer; it now reads `comp.backend.pixels`.
- severity: high (makes CPU per-pixel compositor drawing unusable under the interpreter)
- component: interpreter (CowEnv get_mut / array-field write on nested `me` borrow)
- found: 2026-07-03, building the WM multi-app taskbar live-capture lane

## Summary

Under the self-hosted interpreter (gui/debug driver), drawing through
`HeadlessHostCompositorBackend` (in `src/os/compositor/host_compositor_entry.spl`)
is O(pixels_drawn x total_framebuffer_pixels): each `put_pixel` clones the entire
`self.pixels: [u32]` array. Measured ~28 ms per `put_pixel` at 1024x768
(786432 px). A single `fill_rect(0,0,50,50, ...)` (2500 px) took **71 s**; a
`fill_rect(300x200)` never finished inside 120 s.

`os.compositor.app_content.render_app_content` and `render_frame`'s direct-draw
path both go through `fill_rect` / `draw_text` / `blit_pixels`, which call
`put_pixel` per pixel — so any real WM frame is effectively unbounded under the
interpreter. This is the same root cost that forces the headless
`check-wm-gui-window-drawing-evidence.shs` gate to budget 30-minute timeouts.

## Root cause (hypothesis, from empirical characterization)

The pathology is a `me` method calling another `me` method on the same object:
`fill_rect(me self)` calls `self.put_pixel(...)` (`me self`). The inner `self`
borrow makes the `self.pixels` Arc non-unique, so `CowEnv::get_mut` clones the
whole array on the write — every call. Evidence:

- `backend.clear(...)` — a SINGLE `me` method that writes `self.pixels[i]` inline
  in its own loop (no sub-`me` call) — is O(n): ~5 s for 786432 px (~6 us/px).
- `backend.fill_rect(...)` — a `me` method that calls `self.put_pixel` per pixel
  — is ~28 ms/px (a full-array clone each pixel). 50x50 = 71 s.

So a leaf `me` method writing `self.pixels` inline is fast; a `me` method that
delegates per-pixel to another `me` method is catastrophic.

## Repro

```
# fill_rect(50x50) alone takes ~71s, fill_rect(100x100) times out > 120s:
SIMPLE_EXECUTION_MODE=interpret SIMPLE_EXECUTION_LIMIT=0 OSTYPE=darwin \
  src/compiler_rust/target/gui/debug/simple run <probe>.spl --mode=interpreter
# where <probe> does: backend = HeadlessHostCompositorBackend.new(1024,768)
#                     backend.fill_rect(0,0,50,50, 0xFF223344u32)  # ~71s
```

## Impact / workaround

- Live rendering must avoid the CPU per-pixel backend entirely. The WM multi-app
  taskbar demo (`examples/06_io/ui/wm_multiapp_taskbar_gui.spl`) draws on the GPU
  via `MetalBackend.draw_rect_filled` (one FFI dispatch per rect) instead.
- Where a CPU buffer is unavoidable, keep all writes inline in a single leaf `me`
  method (like `clear`), never `me`->`me` per-pixel delegation.

## Fix direction (not done)

Make `CowEnv::get_mut` (or the array-field write path) not clone when the extra
Arc reference is only the transient inner-`me` `self` borrow of the SAME object
whose field is being mutated — i.e. recognize self-aliasing so a `me`-in-`me`
per-element write stays in-place. Until then, the interpreter cannot support
per-pixel CPU rasterization at interactive sizes.
