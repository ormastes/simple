# `simple_web_renderer_spec.spl`: transplant-lost helpers and rows, 22 red rows left

- Date: 2026-11-15
- Spec: `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer_spec.spl`
- Status: partly fixed (restoration); 22 rows open, triage in progress

## What the release line had

111 rows, 83 passing, 28 failing at `5bc8747b394` and identically at
`71ff31154d5` (diffed by row name on the Nov 14 seed
`cargo-target-webrender-vk/release/simple`, 59635056 bytes).

## Root cause of the first 9: a stale snapshot

`88aac2ffe28` ("rebase(main): transplant current main tree onto release/1.0")
replaced the spec with an older copy (+420/-582 lines). Against its parent it
lost:

- five helpers still called by live rows: `_count_non_color_rect`,
  `_draw_ir_command_index`, `_draw_ir_text_command`, `_wm_material_section`,
  `_wm_material_section_with_backdrop` (8 rows died with
  `function ... not found`);
- the first 29 lines of "renders content visibility hidden containers while
  suppressing descendants" (`partial_html` and five more locals; the row died
  with `variable partial_html not found`);
- three whole rows and their fixtures: "keeps abbr in canonical inline flow",
  "keeps time in canonical inline flow", "lowers text-transform through Draw IR
  to exact uppercase pixels" (the last is still named by
  `test/03_system/check/cpu_simd_render_scale_contract_spec.spl:268`);
- ten imports (`simple_web_layout_render_html_gpu_frame`,
  `..._software_pixels`, `..._readback_paint`, ...). The seed resolves them
  transitively; the self-hosted compiler does not.

`origin/main` carries the same loss (not fixed there by this lane).

Restored from `88aac2ffe28^` verbatim; every restored name was checked to
still exist in `src/lib`. Result: 114 rows, **92 passing, 22 failing**. The
restored rows pass, except the three that now show real values (below).

## Open: 22 rows, preliminary class (each needs evidence before a change)

| class | rows | first symptom |
|---|---|---|
| Draw IR contract / CSS background lowering | cascaded font families; one exact CSS background image; unclipped rounded background; content clip insets per radius axis; positioned sized boxed background shorthand; input values as Draw IR text; transformed themed input text; opacity zero subtree | `simple-draw-ir-v3` vs pinned `v2` (v3 since `8a3479b64ca`); background command kind `rect` vs `image`; computed-style keys empty; `path:0` vs `id:invisible-button` |
| backend-name resolution | supported Engine2D names before fallback; OpenCL selection | `software` returned for `cuda`/`rocm`/`opencl`/`metal`; the row title says "before runtime fallback", so it is not assumed environmental |
| host face | no vector size without a resolved face | the host resolves Liberation Sans (`unmanaged=...LiberationSans-Regular.ttf`); gate like the other face-dependent rows |
| glyph ink | lowercase vs uppercase glyphs; text-raster fixture ink; text-align-last | `0 > 0` ink counts; must not be made green by forcing the upscaled 5x7 bitmap lane |
| one colour level | Aetheric gradient over translucent base; shorthand hex alpha on white | `0xFF787878` vs `0xFF777777`; measure Chrome 159 before choosing |
| paint geometry | object-fit contain; object-position; positioned absolute paint order; leaf background opacity; WM material request bounds; generated widget chrome text | placeholder colour 0 px; 240 vs 600 / 504 vs 144; 0 vs 5776; 800 vs 200 |
