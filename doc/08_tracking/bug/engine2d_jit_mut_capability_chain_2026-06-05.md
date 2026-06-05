# Engine2D/web GUI apps fall back to interpreter: W1006 `mut`-capability JIT-blocker chain

**Status:** OPEN (partial) — 3 functions fixed; JIT does not yet flip to native.
**Severity:** Perf — pure-Simple GUI lane (engine2d CPU + web layout) runs fully
interpreted; `draw_text`/glyph rasterization is the dominant cost, making the GUI
sanity apps slow (tens of seconds to minutes per frame at modest resolutions).
**Affected:** the whole-program JIT path for any app importing the engine2d CPU
backend / web layout renderer (e.g. `examples/06_io/ui/widget_showcase_gui.spl`,
`web_render_page_ppm.spl`).
**Path:** `bug` track.

## Symptom

Every `bin/simple run` of a pure-Simple GUI app prints:

```
[INFO] JIT compilation failed, falling back to interpreter: HIR lowering error:
  Memory safety error [W1006]: mutation without mut capability: mutation requires
  `mut` capability while lowering <fn> at <line>
```

JIT is whole-program: a single un-lowerable function aborts JIT for the entire
run, so everything executes in the (much slower) interpreter. The blocker is the
W1006 pattern — a function takes an array parameter **without** the `mut`
capability and then index-assigns into it (`buf[idx] = ...`). The interpreter
permits this (arrays are reference-like); the JIT capability checker rejects it.

## Fix (per function)

Add the `mut` capability to the mutated array parameter, e.g.:

```
fn render_glyph_to_buffer(mut buf: [u32], ...)   # was: buf: [u32]
```

## Fixed so far (correctness-correct; params genuinely mutate)

- `src/lib/gc_async_mut/gpu/engine2d/glyph.spl` — `render_glyph_to_buffer`,
  `render_text_to_buffer`
- `src/lib/gc_async_mut/gpu/engine2d/backend_emu_math.spl` — `_emu_sort_i32`

## Remaining candidates in the engine2d/browser_engine modules (scan)

```
src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl          _metal_pack_i32_le(buf)
src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_helpers.spl _pixels_to_bytes(pixels), _bytes_to_pixels(pixels)
src/lib/gc_async_mut/gpu/engine2d/helpers_pixel.spl          buf_get_pixel/buf_set_pixel/buf_set_pixel_blend(buf)
src/lib/gc_async_mut/gpu/engine2d/backend_metal_helpers.spl  _pack_i32_le(buf)
src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl  fb_put(fb), fb_clear(fb)
src/lib/gc_async_mut/gpu/browser_engine/simple_web_file_renderer.spl         _fill_white(pixels)
```

The chain extends beyond engine2d into `common/` and `std` (the JIT pulls in the
whole module graph), so fixing the list above is necessary but **not sufficient**
to flip JIT to native this session — judge progress solely by whether the
"falling back to interpreter" line disappears, not by wall-clock (which is
confounded by CPU contention from concurrent renders).

## Notes

- Do not claim a perf win from the partial `mut` fixes: with JIT still failing,
  execution stays interpreted and the annotations give no runtime benefit yet.
- The fixes ARE correct regardless (a mutated param should carry `mut`), and are
  prerequisites for eventual JIT enablement.
- A compiler-side follow-up worth considering: have the W1006 check report **all**
  offending functions in one pass (not just the first) so the chain can be fixed
  in bulk rather than one re-run at a time.
