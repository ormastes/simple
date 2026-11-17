# Web render at device scale 4: residual interpreter per-pixel cost (2026-11-16)

Status: PARTIALLY FIXED 2026-11-17 (items 1 and 3 fixed, pixels byte-identical; items 2 and 4 still open). This is a perf bug, and the output is correct.

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

## 2026-11-17 update: items 1 and 3 fixed

Binary: seed `/home/yoon/.cache/cargo-target-webrender-vk/release/simple`, 59635056 B, mtime 2026-11-14 09:32:20. Page runs use `SIMPLE_EXECUTION_MODE=interpreter`, `PAGE_DEVICE_SCALE=4`, `cpu_simd`, 3600x3040, `/usr/bin/time -v`. Base is `6529dd52212`; both sides ran from sparse worktrees of that tree, with other jobs running in parallel, so wall times are indicative (about +-10%).

| # | Fix | Before | After | Proof |
|---|-----|--------|-------|-------|
| 1 | `emu_draw_shadow_rect`: skip zero-coverage rows/columns, the constant interior is one pixel formula + one `write_span` when the destination segment is uniform (`min()==max()`), only the falloff bands stay per pixel; read only the surface-clipped region instead of the whole frame | evidence-size shadow (3408x728, blur 72, 3600x1300 surface): 31.2 s, 483 MB | 5.7 s, 708 MB (1.2 s of both is surface clear + readback) | digest equal on 8 shadow configs (uniform bg, non-uniform bg, off-surface, no-plateau, legacy alpha-0 colour, blur 1/2, clip) and on the evidence-size case |
| 3 | `encode_ppm_p6`: a flat row, or a flat 64-pixel block of a mixed row, is one `write_span` of a doubling-built RGB pattern; mixed blocks keep per-pixel stores | 3600x3040: 21.0 s, 2.31 GB | 3.4 s, 2.31 GB | bytes equal on 5 shapes (W=150/64/1/700/63, odd tails, alpha-only differences) |

Whole page, base -> head (wall, peak RSS; PPM sha256 identical on all three):

| page | wall | RSS |
|------|------|-----|
| tab-bar | 96.1 s -> 81.3 s | 2.883 -> 2.880 GB |
| evidence | 258.3 s -> 211.5 s | 2.891 -> 2.906 GB |
| forms-media | 305.6 s -> 283.5 s | 2.951 -> 2.919 GB |

The page gain is smaller than the micro gain, so the original "shadow dominates the 113 s box command" presumption was wrong: the shadow loop was about 30 s of it. The remaining evidence/forms-media time was not re-attributed per phase here; items 2 and 4 above are the unmeasured suspects and were not touched.

Trap found (read this before using `slice`/`min`/`max` on a pixel array in the interpreter): a read method (`slice`, `min`, `max`) interleaved with `write_span` on the SAME array re-decodes the whole backing store. Measured 11-13 ms per `slice` and 7-10 ms per `write_span` on a 3.66 M-pixel array, 16.5 s of the 19 s row loop of the first version of fix 1. Reading a never-written `src` and writing a separate `outp` made it 2.3 s. The fix keeps a read-only `src` plus a write-only `outp` (two region-sized arrays); the isolated evidence-size run grew 483 -> 708 MB, the page peaks moved by -1.1 % to +0.5 %. Interpreter bug record: `doc/08_tracking/bug/interpreter_array_read_after_write_redecodes_backing_2026-11-17.md`.

Not done:
- Item 2 (glyph raster): not investigated; the cache key/atlas policy belongs to the font-renderer owner. Glyph shapes are untouched.
- Item 4 (full-frame fills) is untouched.
- Shadow falloff bands are still per pixel (2.3 s in the evidence-size case). When the whole region is one colour, rows with equal `cov_y` are identical and could be copied with `write_span`; not done to keep the change small.

Catalog gate, head, `sh scripts/check/check-chrome-catalog-pixel-diff.shs --device-scale 4`: `PASS — 8 page(s) compared, worst=5.56, all within baseline ...Linux-aarch64.dpr4.txt (+0.25)`. The PPM sha256 of all 8 pages equals the base run (`6529dd52212`), so every page is byte-identical; the two rows that differ from the baseline file (animation 4.14 -> 4.17, tab-bar 0.54 -> 0.30) differ identically on base, i.e. they are older drift, not this change. Evidence phases at head (concurrent load): render 204 s, PPM encode 2 s, write under 1 s.
