# Web renderer: the Vulkan lane paints some glyphs one row lower than the CPU lane

Status: FIXED 2026-11-15 on `work/engine2d-vulkan-text-20261115` (base
`830879893c3`). Found the same day on `work/engine2d-lane-parity-20261115`
(base `fa2dd425635`), while listing every cpu_simd vs Vulkan (llvmpipe)
difference on the web catalog.

## Lane census (900x760, same seed, pixels with any channel off by more than 1)

Seed `$HOME/.cache/cargo-target-webrender-vk/release/simple` (59635056
bytes, 2026-11-14 09:32:20 +0900), `check-chrome-catalog-pixel-diff.shs`
`--backend cpu_simd` and `--backend vulkan` with
`VK_DRIVER_FILES=/usr/share/vulkan/icd.d/lvp_icd.json`; ppm-vs-ppm diff.

| page        | differing px | largest region                   | max |
|-------------|--------------|----------------------------------|-----|
| overview    | 2            | x480-495 y192-207                | 29  |
| html        | 2            | x128-143 y160-175                | 40  |
| css-layout  | 26           | x48-95 y368-383 (22 px, one row) | 125 |
| css-paint   | 0            |                                  |     |
| forms-media | 25           | x96-143 y144-159 (24 px)         | 232 |
| animation   | 1            | x240-255 y576-591                | 14  |
| evidence    | 0            |                                  |     |
| tab-bar     | 6            | three 1-4 px sites               | 131 |

62 pixels across 8 pages; the Chrome mismatch percentages are identical per
page in both lanes. Every site inspected is text ink: the Vulkan lane draws
a glyph row (or a descender) that the CPU lane does not. Chrome 159 agrees
with the CPU lane at the checked pixels (forms-media row 145 white,
css-layout (55,376) #64738a vs CPU #627289, Vulkan #172033).

The Engine2D primitives themselves agree: `feature_showcase.spl` (38
primitives, including `draw_gradient_rect_stops`) is byte-identical between
`VK2D_BACKEND=cpu` and `VK2D_BACKEND=vulkan` on llvmpipe (1,920,000 bytes).

## Repro (25 px)

`examples/06_io/ui/web_catalog/forms-media.html`'s `<style>` plus
`<label>Name <input value="Simple"></label><label>Choice <select><option>Alpha</option></select></label>`,
rendered 300x120 through `simple_web_render_html_to_pixels_with_engine2d_backend`
on `cpu_simd` and on `vulkan` (llvmpipe, interpreter): 25 differing pixels,
first at (60, 32). In the `<input>` value some glyph columns end at y 31 on
both lanes (x 67) while others (x 70, 74, 78) reach y 32 on Vulkan only: the
extra row is per glyph, not a uniform clip edge. Root cause not found.

## Root cause

Not a clip-edge off-by-one, glyph height or blit height: the Vulkan
vector-face composite ignored the clip rect entirely.

The Draw IR text branch (`engine2d/draw_ir_adv.spl`) sets
`Engine2D.set_clip` to the command's clip (the `<input>` control box, bottom
row y 31) and calls `draw_text_with_advances`. On the Vulkan lane that reaches
`VulkanBackend.composite_font_batch` (`engine2d/backend_vulkan_font.spl`),
which dispatched every staged glyph quad whole. Only the BITMAP text path
applied `vulkan_bitmap_text_clip_quads`; the CPU lane clips in
`draw_image`. Glyphs whose quads ended at y 32 gained one row; the 'p'
descender (quad y 26-35) gained four, which is why the extra ink looked
"per glyph". Narrower repro: the forms-media `<style>` plus
`<label>Name <input id="name" name="name" value="Simple"></label>`, 300x120,
24 differing pixels.

RenderDoc capture on llvmpipe (both runs `num_captures=1`, same 34
dispatches): only the font-atlas composite's params buffer differs. Glyph
rows before y 23-32 (p: 26-35), after y 23-31. Table and method:
`doc/00_llm_process/feature_expert/simple_renderdoc/skill.md`.

## Fix

- `composite_font_batch` intersects every quad with `self.clip_*` through
  `vulkan_bitmap_text_clip_quads` before partitioning and dispatch, and
  reports the caller's quad count so the batch is admitted without a CPU
  redraw.
- A batch whose quads are ALL outside the clip returns the new status
  `clipped-out` (zero dispatches), admitted by both
  `engine2d_vulkan_font_batch_admits` and its twin
  `vulkan_font_batch_composited`. Before that change it fell back to the CPU
  (`font_execution_target()` == `cpu`) and `draw_text_with_advances_vulkan_only`
  returned false. Such a batch uploads nothing, so the host atlas mirror is
  marked stale when the batch carried new cells.
- Twin repair found on the way: `vulkan_font_batch_composited` never gained
  `promoted` when `engine.spl` admitted it (`10b231914cf`), so
  `backend_vulkan_bitmap_text_atlas_spec` was 5/6 at the base.

Evidence: `test/01_unit/lib/gc_async_mut/gpu/engine2d/vulkan_text_advances_clip_parity_spec.spl`
(red at the base: 10 px below the clip; red without `clipped-out`: target
`cpu`, vulkan-only `false`; 3/3 after). Repro 24 -> 0 px. Catalog 900x760 on the fixed tree: all 8 pages
byte-identical between `--backend cpu_simd` and `--backend vulkan` (llvmpipe)
`.ppm` files (`cmp`), was 62 px; the cpu_simd gate still PASSes (worst 7.09).
forms-media Vulkan work is unchanged (39 font composites, pack_full=12,
pack_incremental=9 before and after); wall-time deltas between runs were not
attributed (shared host).

Review follow-ups (same day):

- With a clip set, `composite_font_batch` copies the quads and the batch only
  when some quad crosses the clip (`vulkan_font_quads_within_clip`); Draw IR
  sets a clip for every control text run, and nearly all of them lie inside
  it. forms-media 900x760 on vulkan (llvmpipe), `simple run` of a one-page
  render, same seed: before 81.10 s / 75.63 s (load ~4, maxrss 1.08-1.11 GB),
  after 84.60 s / 87.02 s (load ~7, maxrss 1.06-1.09 GB), pixel checksum
  identical (`sum=2697697746427296`). The page is dominated by other work and
  the host load doubled between the runs, so no wall-time win is claimed; the
  change removes one quad array plus one `FontRenderBatch` copy per
  inside-clip run.
- New rows: left/top partial clip (atlas read position shifted, byte-equal to
  software), a run whose origin is off the top-left, host rows for the clip
  helpers (atlas_x/atlas_y shift on left/top trim, negative origin, exclusive
  right/bottom edges), and a Draw IR row proving valid advances are applied
  (encoded `7,7` == `[7, 7]`, != `[3, 11]`; the advances must sum to the
  command width or the run falls back to the font's own advances).
- The Vulkan rows print `[skip] <row>: no llvmpipe ICD at
  /usr/share/vulkan/icd.d/lvp_icd.json; this Vulkan row was not exercised`
  when the ICD is missing. A green run on such a host is not Vulkan evidence.
