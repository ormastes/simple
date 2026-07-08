# Browser Layout Large SIMD Fill Facade Unsafe

- **Date:** 2026-07-09
- **Status:** open
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
