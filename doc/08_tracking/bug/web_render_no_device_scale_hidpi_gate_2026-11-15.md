# Web renderer has no device scale, so the Chrome gates cannot run at high DPI

- Date: 2026-11-15
- Area: `src/lib/gc_async_mut/gpu/browser_engine/`, `scripts/check/check-chrome-catalog-pixel-diff.shs`,
  `scripts/check/check-web-combo-matrix-chrome.shs`
- Status: open (filed by the web-render residue lane; not implemented there)

## Owner rule this blocks

Render check tests should compare at 300 dpi or more (Chrome
`--force-device-scale-factor` >= 3.125, 4 preferred) or with a 1-pixel bitmap
font shared by both sides. A test or perf number must never be passed by
enlarging the font. Both sides use the same font.

## Measured state

- Both gates force Chrome to `--force-device-scale-factor=1`
  (`check-chrome-catalog-pixel-diff.shs` viewport probe and page shots,
  `check-web-combo-matrix-chrome.shs` harvest flags).
- `browser_engine` has no device-scale concept: `grep device_scale|device_pixel_ratio`
  over `src/lib/gc_async_mut/gpu/browser_engine` and `src/app/ui/chrome_showcase`
  finds nothing. Layout is integer CSS px (`[i32]` boxes, `font_size: i32`,
  `resolved_font_advances: [i32]` per codepoint), and the rasters paint one
  device pixel per CSS px.
- Fonts on this host (Linux aarch64): Simple's measured face set is Liberation
  Sans / Serif / Mono (`browser_host_has_measured_linux_face_set`,
  `src/lib/nogc_sync_mut/text_layout/font_provider.spl`). Chrome is not given a
  pinned file: it resolves `sans-serif` / `serif` / `monospace` through
  fontconfig (its defaults alias to Arial / Times New Roman / Courier New,
  which fontconfig maps to the same Liberation files here). It is the same
  face only by host configuration. The headless shell does NOT match:
  it resolved `<code>`'s monospace to a 1 px shorter line box (fontconfig
  `monospace` = DejaVu Sans Mono here), which made 28 matrix ids mismatch at an
  untouched base. The gates must run the full browser
  (`CHROME_BIN=.../chromium-1255/chrome-linux-arm64/chrome`, `CHROME_NO_SANDBOX=1`).
- No fixture or spec enlarges fonts to hide a mismatch. Catalog pages use 16px
  body and 24px headings, no `@font-face`. `test/fixtures/browser/anon_v1.html`
  (`<code style="font-size:40px">` in a nested list) is a minimal repro of a tall
  inline box in a list item; it has no consumer in `test/`, `scripts/` or
  `src/`, so it is not used by any gate. `style_cascade_memo_spec.spl`'s
  40px div checks em inheritance in the cascade memo, not pixels.

- Upscaled bitmap face (owner clarification: 1:1 bitmap or >= 300 dpi, never
  a bitmap blown up): the Simple renderer still carries the 5x7 bitmap lane
  (`common.ui.glyph_bitmap_5x7`, `fb_text_sparse_range`), and it IS an upscaled
  bitmap: `web_glyph_scale(fs) = max(1, fs / 8)` paints each font pixel as a
  2x2 block at 16px. The catalog and matrix gates do not take it: the render
  entries default `vector_fonts = true` (`compute_styles(..., vector_fonts:
  bool = true)`), and the matrix compares layout geometry only, no raster.
  Not traced exhaustively: which unit specs pass `vector_fonts = false`; any that do
  must not be read as Chrome pixel evidence.

## Design (minimal device scale)

1. A `device_scale_milli: i32` (1000 = 1x) carried by the render entry points
   (`simple_web_render_html_to_pixels_*`, `pixel_diff.spl --simple-only`) and a
   `--device-scale` flag on the catalog gate that sets both Chrome
   `--force-device-scale-factor` and the Simple value, with its own baseline
   file `chrome_catalog_pixel_diff_baseline.<os>-<arch>.dpr4000.txt`.
2. Layout stays in CSS px. Scale is applied at the layout -> raster boundary:
   each box edge maps to `round(edge * scale)` (snap edges, not sizes, so
   neighbours share a device edge like Blink's pixel snapping).
3. Text rasterises at `font_size * scale` from the TTF outlines (the glyph
   atlas keying by size is not verified), positioned from milli-px pen advances
   scaled, not from the per-codepoint `[i32]` rounding. The 5x7 bitmap lane
   is not scaled up: it must not be used at high DPI (that would be the
   "big-pixel font" the rule forbids).
4. Borders / outlines: device width `max(1, round(w * scale))` for non-zero
   widths, matching Chrome's hairline rule.
5. Gradients, shadows, radii evaluate in device px from scaled geometry.

Size: the paint lanes (fb raster, Draw IR, Vulkan present) each read box
geometry directly, so the change touches every painter. That is more than a
residue lane carries; it needs its own lane with a red spec per painter (a
4x render of a 10x10 bordered box and one glyph row against Chrome 4x).

## Alternative allowed by the owner

A 1-pixel bitmap font fixture used by both sides: Chrome needs the same glyphs
as a real font file (`@font-face` with a bitmap-outline TTF, one square contour
per set pixel), and Simple's 5x7 lane would have to read the same file instead
of its built-in table. Not started.
