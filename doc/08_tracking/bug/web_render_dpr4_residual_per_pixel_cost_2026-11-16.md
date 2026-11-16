# Web render at device scale 4: residual interpreter per-pixel cost (2026-11-16)

Status: OPEN. This is a perf bug, and the output is correct.

The k^3 framebuffer-copy-per-span cost is fixed: whole-frame extern marshalling
was removed from `backend_software.spl`. See the 2026-11-16 note in
`doc/00_llm_process/feature_expert/web_render_css_parity/skill.md`. What remains
is linear per-pixel work that the interpreter executes one pixel at a time.

Measured after the fix:
- seed `/home/yoon/.cache/cargo-target-webrender-vk/release/simple`, 59635056 B
- cpu_simd backend on an aarch64 host, `SIMPLE_EXECUTION_MODE=interpreter`, 3600x3040 target
- per-command times from a temporary timer in `_engine2d_draw_ir_render_command_plan`

| # | Cost | Where | Measured |
|---|------|-------|----------|
| 1 | Outer box-shadow per-pixel loop | `emu_draw_shadow_rect` (`backend_emu_adv.spl`). It visits every pixel of the (w+4r)x(h+4r) region in Simple. | evidence `<section>` (3408x728, blur 72, radius 48): 113 s of 223 s paint for the WHOLE box command (shadow + rounded fill + border, not split). The shadow loop (about 3.75 M px) is presumed dominant, because the fill and border now go through fast spans. |
| 2 | Glyph raster at 64 px (16 px CSS x4) | Font atlas fill on a cache miss | evidence 'Evidence contract' (17 glyphs) 35 s; tab-bar text 33 s of 69 s paint. A miss costs about 1-2 s per glyph; a hit costs well under 0.1 s. |
| 3 | PPM encode | `encode_ppm_p6` (`common/image/ppm_decode.spl`), 3 stores per pixel | 21 s at 10.9 M px (1.3 s at K=1) |
| 4 | Full-frame opaque fill | `sw_fill_raw_span` per row (batch build, kernel lookup, row alloc) | 6-7 s per 3600x3040 fill. `clear()` plus the page background is about 13 s. |

Failing scenario: `sh scripts/check/check-chrome-catalog-pixel-diff.shs --device-scale 4`
still spends about 4 min (evidence) to about 1.5 min (tab-bar) per page on the Simple side.
The heavier pages (css-layout, forms-media, animation) were not re-measured.

Not done here, and why:
- **1:** must stay byte-identical to the emu reference formula. A bulk kernel
  needs either a native shadow span ABI or a pure-Simple restructuring that skips
  the zero-coverage band with `write_span`. The band is about 36 px per side at
  r=72, which is small.
- **2:** belongs to the font-renderer owner, and the cache key/atlas policy is
  out of scope for a pixel-identical perf change.
- **3:** needs a bulk [u32] -> RGB [u8] primitive. No such primitive exists in
  pure Simple today.
