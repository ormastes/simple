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

## Batch 3a (2026-11-15): 3 rows gated as host-dependent, 19 left

Class (c), environment-dependent — gated, no assertion removed:

- **Backend names (2 rows).** `cuda`/`rocm`/`opencl`/`metal` returned
  `software` because `simple_web_engine2d_resolved_backend_name_with_reason`
  probes the real device and falls back honestly (contract made explicit in
  `9970185d1de`, which only surfaced the reason; the `"software"` fallback is
  older). Measured on this host (aarch64, seed 59635056 bytes): `cuda -> cuda`,
  `vulkan -> vulkan`, `cpu_simd -> cpu_simd`; `hip -> software` ("ROCm/HIP
  runtime, device, or module unavailable"), `opencl -> software`
  (`opencl-context-create-failed`), `metal -> software` ("Metal requires
  macOS"). The rows now expect the canonical name where an independent
  `Engine2D.probe_backend` initializes and `software` otherwise; the alias
  `hip -> rocm` is asserted host-independently through `backend_canonical_name`.
- **Host face (1 row).** Gated on `browser_host_has_measured_linux_face_set()`
  like the other face-dependent rows: with the Liberation set the identity is
  `LiberationSans-Regular.ttf` at 17 px; elsewhere the old `""`/`0` pin stands.

Run: `95 passed, 19 failed` of 114 (was 92/22).

## Batch 3b (2026-11-15): 4 more rows, 15 left

- **Glyph ink (3 rows), stale pins re-measured against Chrome 159 (class a).**
  The rows asserted exact text-colour pixels > 0 at 8 px, which is a property
  of the upscaled 5x7 bitmap face, not of a real one. Full Chrome 159
  (chromium-1255, same Liberation files) paints **0** exact-colour pixels at
  8 px: `#111827` "chrome baseline" 0 exact / 226 ink pixels;
  text-align-last 0 exact / 244 ink; the text-raster subtitle `#475569` 0
  exact (its 16 px title has 15 exact `#0f172a`). Simple's vector face does
  produce ink (203 non-white pixels at 8 px, darkest `#1e2434`); it was never
  "no ink". The rows now assert ink (pixels different from the background,
  inside the text band) and keep the lower-vs-upper and left-vs-right
  inequality checks. The 5x7 face was not forced.
- **Shorthand hex alpha (1 row), real defect (class b).** `#0008` over white
  is `#777777` in Chrome 159 (re-measured; pin was right). The Draw IR compose
  path used `_web_canvas_background`, which blends the quantized byte with a
  256 denominator (`#787878`). It now uses `web_canvas_background_authored`,
  the raster lane's authored-fraction compositor (8/15 for `#0008`).
- **Aetheric gradient pin is NOT Chrome.** Chrome 159 paints `#575758` /
  `#585859` on row 0 and `#535354` / `#525253` on row 1; the pin says
  `#595959`, Simple paints `#5a5a5b`. Chrome samples vertical ramps at row
  centres (4 px `#000->#fff` = 1F/60/9F/DF); the CPU raster ramp is
  endpoint-exact since `92b33870986`, which was tuned to spec pins, not to
  Chrome. Open: fix the ramp and re-pin to Chrome in its own change.

Run: `99 passed, 15 failed` of 114.

## Batch 3c (2026-11-15): 3 more rows, plus a race fix; 12 left

- **Leaf opacity (real defect, class b; introducing commit `ece10b378c8`,
  2026-08-16).** That commit replaced "scale the child's per-pixel alpha by the
  group opacity, then source-over" with `engine2d_composite_region_milli`,
  which blends the child at a constant `a8` and ignores the child pixel's own
  alpha. A single opacity root gets a full-viewport embedding, so every
  transparent child pixel darkened the parent: `#f8fafc` became `0x807c7d7e`
  across the frame (Chrome 159: 5776 `#f8fafc`, 240 `#8ba4ea`, 128 `#22c55e`,
  0 `#ef4444` — the pins). Fix: `ea = src_alpha * a8 / 255`, so an opaque
  source keeps `ea == a8` and the oracle values that commit pinned.
  `fractional_subtree_opacity_spec` 1/2 -> 2/2; `engine2d_embedded_surface_spec`
  and `browser_chrome_embedded_rendering_spec` unchanged vs base (8/10, 6/6).
  Older trees cannot be bisected with this seed (they fail HIR lowering), so
  the commit was found from the code, not by bisection.
- **Absolute paint order (real defect).** Chrome 159 equals every pin. The
  Draw IR paint order lifted only `position:absolute` with `z-index > 0`; a
  positioned box with `z-index:auto/0` painted in tree order under later
  in-flow siblings. Positioned boxes (absolute/fixed/relative) with
  `z-index >= 0` now paint after the in-flow content of their context
  (CSS 2.1 Appendix E). Known ceiling (`# ponytail:` in source): a z-auto box
  is grouped like a context, so a positive-z descendant sorts inside it.
  Negative z-index is unchanged.
- **Input box kind (stale pin, class a).** The row pinned `kind == "box"`;
  Draw IR has never had a `box` kind (rect/text/edge/path/image/group/port).
  Corrected to `rect`.
- **Backend-name rows made race-free.** The 3a gate compared against a
  separate `Engine2D.probe_backend`; on the shared GPU cuda probed
  Initialized and then resolved to `software` (load 23). The rows now take
  name and reason from one `simple_web_engine2d_resolved_backend_name_with_reason`
  call: canonical name with no reason, or `software` with a reason. The
  `create_with_backend` name must be the canonical name or `software`.
- **Font-family row is not culling.** At 160 px the shorthand span starts at
  x=163 and is correctly culled. Chrome 159 with the same bundled
  `PixelifySans[wght].ttf` measures "Override" at 56.86 px (per glyph at
  16 px: O 11.55, v 8.00, e 7.10, r 5.33, i 4.45, d 8.00); Simple resolves the
  same face (sha256 `9ba86cd0...`, wght=400) and measures 69 px. Open: the
  Pixelify advance widths. Noto Sans Mono (77) and Liberation Sans (61) match.

Run: `102 passed, 12 failed` of 114 after the race fix (101/13 before it: the
cuda race flipped a green row red). The opacity-zero row (`path:0` vs
`id:invisible-button`) is still open, separate from the composite fix.
