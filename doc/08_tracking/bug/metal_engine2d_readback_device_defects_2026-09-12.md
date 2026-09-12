# metal_engine2d_readback: 4 stale spec oracles, 0 Metal device defects (2026-09-12)

**Status:** RESOLVED (spec corrected). **Spec:** `test/02_integration/rendering/metal_engine2d_readback_spec.spl`.

**Headline, stated plainly: no Metal backend defect was found.** All four
failures were stale oracles in the spec — three blend values that predate the
`color.spl` unpremultiply fix, and one completeness polarity that predates the
glyph-atlas kernel. On this Apple M4, with the seed
`build/cargo-r2/release/simple` (39,178,424 B, mtime 1789197971) built *with*
the `metal` feature, the CPU mirror and the Metal device agree bit-for-bit in
every failing case. Zero lines of `backend_metal*.spl` / `backend_metal_msl.spl`
were changed. Result: **13 examples, 0 failures** (12 -> 13; one example added).

## The three blend failures (rect_filled, circle_filled E1, triangle_filled E2)

All three read `0x101E2D3C` where the spec expected `0x101F2F3F`. The measured
value is *exactly* what the frozen CPU reference produces:

```
blend(0x01020304, 0x10203040)  # engine2d/color.spl:74
  sa=1, da=16, inv=254
  dst_weight = (16*254)/255      = 15
  out_a      = 1 + 15            = 16   (0x10)
  out_r      = (2*1 + 32*15)/16  = 30   (0x1E)
  out_g      = (3*1 + 48*15)/16  = 45   (0x2D)
  out_b      = (4*1 + 64*15)/16  = 60   (0x3C)
=> 0x101E2D3C
```

Probed directly (interpreter, this seed): `blend(...)` = 270413116 = 0x101E2D3C,
and mirror == device == 270413116 for rect_filled, circle_filled and
triangle_filled alike. `blend_src_over` in `backend_metal_msl.spl:240-256` is a
statement-for-statement transcription of `color.spl:74-115` — it was already
correct.

`0x101F2F3F` is the *pre-unpremultiply* formula `src*sa/255 + dst*(255-sa)/255`
(= 31/47/63). It rotted when `color.spl` started compositing in premultiplied
space and unpremultiplying by `out_a` — the change recorded in
`engine2d_straight_alpha_transparent_destination_blend_2026-07-11.md`, which
updated some anchors and missed this spec. Changing the MSL to reproduce
`0x101F2F3F` would have broken the frozen CPU twin; the spec was the thing that
was wrong.

Note on the rect case specifically: `expect(pixels[4+4*16]).to_equal(0x01020304)`
(a raw store) was wrong on a second count too. CPU `draw_rect_filled` routes
`alpha < 255` through `sw_hline_blend` (`backend_software.spl:391-400`), so the
blend the Metal kernel performs is the correct twin behaviour. The example now
also draws an *opaque* `0xFF020304` rect so the `sa == 255` raw-store
short-circuit keeps a literal-word oracle of its own.

## The draw_text failure (W4)

`expect(b.gpu_frame_complete).to_equal(false)` — which contradicted the
example's own title, "stays GPU-complete". Measured: `pipe_glyph_atlas_blit=19`,
`glyph_lut_buffer=27`, `read_pixels_with_source().source == "device_readback"`,
`gpu_frame_complete == true`, 18 lit pixels, device == mirror everywhere. The
atlas dict **is** uploaded and the kernel **is** dispatched. The `false` oracle
recorded the pre-atlas CPU-fallback lane and only looked right on a seed built
without the `metal` feature. The example now pins absolute values: a lit pixel
is the literal `0x01020304` (glyph writes are raw stores, matching
`sw_set_pixel`), an untouched pixel is the literal `0x10203040`, and exactly 18
pixels are lit.

## F26 correction: the rounded-rect coverage term is NOT dropped on the device

F26 reported hard edges on the Metal device, which would mean the kernel ignored
`_rr_cov256`. It does not. `draw_rounded_rect(2,2,12,12,4,0xFFFF0000)` over
opaque black yields a full anti-aliased arc on the device, matching the mirror
pixel-for-pixel: (3,2)=0xFF320000, (4,2)=0xFFB10000, (5,2)=0xFFF60000, with
(7,7) solid fill and (1,1) background. A new example pins (3,2) == 0xFF320000 on
both lanes, plus the not-bg / not-fill intermediacy the F26 claim denied.

## Sabotage quadruple (each caught exactly its own example, then restored)

| sabotage in `backend_metal_msl.spl` | expected red | observed |
|---|---|---|
| `kernel_draw_circle_filled` -> raw store | E1 | `13 examples, 1 failure` (E1) |
| `kernel_draw_rect_filled` -> raw store | rect_filled | `13 examples, 1 failure` (rect) |
| `_rr_blend_cov`: `a_eff = (a*cov)/256` -> `a_eff = a` | F26 | `13 examples, 1 failure` (F26) |
| `kernel_glyph_atlas_blit` raw store -> `blend_src_over` | W4 | `13 examples, 1 failure` (W4) |

Method note worth keeping: the first attempt at the fourth sabotage used a
non-global `perl -0pi -e 's///'`, which silently patched
`kernel_draw_rounded_rect_outline` (the first match in the file) instead of the
glyph kernel and produced a *green* run. A sabotage that stays green must be
verified as having actually landed on the intended line (`git diff -U0`) before
it is read as "the oracle does not discriminate".

## Adjacent findings (NOT fixed here — Vulkan and its docs are frozen for this lane)

1. **The Vulkan compute blend still uses the old formula.**
   `backend_vulkan_glsl.spl:638-651` computes `out_r = (s*sa + d*inv)/255` with
   no `da` premultiplication and no unpremultiply by `out_a`, so it produces
   `0x101F2F3F` for the anchor above — diverging from the CPU reference and from
   Metal. `backend_vulkan_spirv_raster_blobs.spl:2145` claims it matches
   `color.spl`'s `blend()`; for the alpha term it does, for RGB it does not.
2. **Stale anchors in peer-owned docs:** `0x101F2F3F` is pinned as the src-over
   anchor in `doc/03_plan/ui/rendering/draw_ir_multibackend_plan.md:10,75`,
   `doc/05_design/ui/rendering/draw_ir_multibackend_design.md:161,169,218` and
   the generated `doc/06_spec/.../metal_engine2d_readback_spec.md`.
3. **Pre-existing, unrelated red:**
   `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_font_spec.spl` is
   `9 examples, 1 failure` — "rejects destination coordinate overflow before ABI
   packing", `expected true to equal -2147483648`, i.e.
   `font_destination_origin(-2147483648, 0, 2).?` evaluates to `true`. Device-free
   and reproduced with zero `src/` modifications, so it is not caused by this
   change. `metal_msl_pipeline_spec` is 7/7.
