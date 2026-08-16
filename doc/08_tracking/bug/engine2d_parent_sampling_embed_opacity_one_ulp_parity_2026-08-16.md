# BUG: parent-sampling glass embed opacity (930) is one ulp off the spec oracle

- id: engine2d-parent-sampling-embed-opacity-one-ulp-parity
- date: 2026-08-16
- area: rendering / engine2d / draw-ir / glass materials
- severity: low (single-channel ±1 rounding on inactive-window glass)
- status: open

## Symptom

`test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_adv_spec.spl:1656`
("preserves 500 and inactive 930 embedding opacity while sampling the painted
parent") fails only its 930 (inactive) assertion:

```
expected 4285953791 (0xFF7676FF) to equal 4285887999 (0xFF7575FF)
```

R and G are one high. The 500 (half) assertion in the same example passes
under the JIT test harness (and is itself one LOW — 0xFF3E3EFF — under the
pure interpreter, showing the SIMD and scalar blends already disagree by one
ulp on this pipeline).

## Where

The parent-sampling translucent embedding branch:

- `src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl:2551-2626`
  (`samples_parent and embedding_opacity < 1000` branch of
  `_engine2d_draw_ir_render_batch_embedded`): seeds an offscreen delta from
  the painted parent, renders the glass material, then composites the core
  back via `eng.draw_ir_composite_readback(..., embedding_opacity)`.
- `src/lib/gc_async_mut/gpu/engine2d/engine.spl:2599-2618`
  (`draw_ir_composite_readback` CPU arm): approximates the milli opacity as
  `engine2d_scale_pixel_alpha` (alpha = a*om/1000, floor, engine.spl:116-128)
  followed by `draw_image_blend`, i.e. two successive /255 (scalar) or >>8
  (SIMD span, `rt_engine2d_simd_blend_span_u32`) floors.
- Scalar reference blend: `src/lib/gc_async_mut/gpu/engine2d/color.spl:74-119`.

## Analysis

The spec's oracle pair (half=0xFF3F3FFF, inactive=0xFF7575FF) is consistent
with a material-over-parent value F=126 composited at EXACT milli weight
(126*500/1000=63, 126*930/1000=117). The current CPU path computes the
opacity through an 8-bit alpha approximation (930 -> 237/255) and lands one
high (118) for 930 while matching 500 by coincidence of rounding. Neither the
scalar `blend()` (/255) nor the SIMD span (>>8) reproduces the oracle for
both opacities through the alpha-scale-then-blend composition.

Fixing this honestly requires deciding the canonical rounding contract for
milli-opacity compositing shared by:
- the CPU scalar `blend()` (color.spl),
- the native SIMD span kernel `rt_engine2d_simd_blend_span_u32`
  (src/compiler_rust/runtime), and
- the Vulkan/Metal blend-checked paths (`draw_vulkan_image_blend_checked`,
  `draw_metal_image_blend_checked`),
in the spirit of commit 00f7ef24528 ("CPU thick-line matches Vulkan kernel
exactly"). A local tweak to only one path would silently break SIMD/scalar
parity elsewhere.

## Unblock condition

Define (and pin with a spec) the exact integer formula for compositing a
readback at `opacity_milli` over an opaque destination — a milli-exact
`out = (src*om + dst*(1000-om) + r)/1000` composite entry point on the shared
kernel, implemented identically in scalar, SIMD span, and device kernels —
then route `draw_ir_composite_readback`'s CPU arm through it instead of
alpha-scale + `draw_image_blend`. When all three implementations agree on the
oracle pair (0xFF3F3FFF at 500, 0xFF7575FF at 930), this example goes green
without weakening any assertion.

## Repro

```
bin/simple test test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_adv_spec.spl
# or interpreter-mode single-path repro used during triage:
# render the spec's 12x12 BLUE parent + window-surface-glass box at
# embedding opacity 500 / 930 and read pixel (5,5).
```
