# Browser Layout Large SIMD Fill Facade Unsafe

- **Date:** 2026-07-09
- **Status:** contained
- **Severity:** high
- **Area:** Simple Web layout, CPU-SIMD, runtime facade

## Summary

The retained 4K/8K Simple Web CPU-SIMD trace shows paint/fill bandwidth is the
remaining bottleneck, but the browser layout renderer cannot safely call the
current Engine2D SIMD fill externs directly for a full framebuffer.

## Evidence

`doc/09_report/cpu_simd_text_glyph_inline_perf_2026-07-09.md` records:

- Retained 8K trace: `paint_ms=776`, total `779724us`, checksum
  `sum32:135445232233405312`.
- Follow-up split trace: 4K `framebuffer_init_ms=188`, `paint_draw_ms=15`,
  `paint_ms=204`, checksum `sum32:32105444634193792`; 8K
  `framebuffer_init_ms=1503`, `paint_draw_ms=32`, `paint_ms=1535`, checksum
  `sum32:135445232233405312`. Both kept 300 DPI retina metadata, full physical
  size, and `screen_size_reduced=false`.
- `simd_fill_row` over a browser-layout framebuffer logged
  `unknown extern function: rt_engine2d_simd_fill_u32`, changed checksum, and
  slowed 4K trace to `878028us`.
- `engine2d_simd_fill_row_u32` over the full framebuffer segfaulted at 4K.
- Routing the 4K benchmark through
  `simple_web_layout_render_html_pixels_engine2d(..., "cpu_simd")` also fails
  before measurement with `unknown extern function: rt_engine2d_simd_fill_u32`,
  so the existing DrawIR fast path does not provide a safe browser-layout fill
  owner boundary yet.
- A safer owner-boundary experiment that routed `fb_rect`/`fb_rect_clip` row
  fills through `backend_software`'s existing `simd_fill_row` owner compiled and
  preserved checksum (`sum32:32105444634193792` at 4K,
  `sum32:135445232233405312` at 8K), but regressed 8K to `1543525us`, so it was
  rejected and reverted.
- Native `rt_array_repeat` now mitigates the framebuffer initialization path by
  filling the allocated backing words directly instead of pushing once per
  pixel; the Rust runtime mirror uses the same no-push shape. Clean sequential
  trace after the C native change: 4K `paint_ms=199`, total `202984us`; 8K
  `paint_ms=765`, total `768514us`, with unchanged checksums and no screen-size
  reduction. This does not expose a safe mutable Engine2D fill facade.
- Browser layout now routes full-frame base fills through returned-array
  `rt_u32_alloc_filled(len, fill)` instead of direct mutable Engine2D SIMD
  fill. The native C helper stores tagged integer pixels, the Rust runtime
  mirror uses `RuntimeValue::from_int`, and the interpreter helper accepts
  signed/unsigned numeric values through `Value::as_int`. The focused scale
  contract passes for default 300 DPI and explicit DPI override with checksum
  parity and full nonzero pixel proof.

The existing row-returning facade is proven only for small evidence rows
(`count=64`) in `src/lib/nogc_sync_mut/gpu/engine2d/simd_kernels.spl`.
Framebuffer-scale browser layout fill needs a safe owner facade instead of
directly calling the Engine2D internals.

## Expected

Either:

- browser layout gets a safe, checksum-preserving framebuffer fill facade with
  retained 4K/8K evidence, or
- the renderer keeps using pure Simple framebuffer initialization and the
  external Cairo gap remains open.

## Next Step

Design the facade at the runtime/Engine2D owner boundary so native builds can
fill a browser-layout `[u32]` framebuffer without missing externs, returned-array
segfaults, checksum drift, or GPU backend behavior changes.

## 2026-07-09 containment

The canonical public row-fill facade was changed to stop exposing the unsafe
mutable extern path. `simd_fill_row` now uses the safe return-row SIMD ABI and
scatter writeback for row-sized fills, with interpreter and native spec coverage
in `test/01_unit/lib/gpu/engine2d/simd_kernels_spec.spl`.
The interpreter no-op registration for the mutable fill extern was removed too,
so accidental direct use fails closed instead of silently reporting fallback.

This is a correctness containment only. Browser layout full-frame base fill no
longer uses the unsafe mutable Engine2D extern path, but a lower-level mutable
typed-array owner bridge is still required before claiming Cairo-class fill
bandwidth.
