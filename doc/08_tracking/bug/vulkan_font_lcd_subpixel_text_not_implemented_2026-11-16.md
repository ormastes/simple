# Vulkan font batch has no LCD subpixel text (CPU lanes do)

Status: OPEN 2026-11-16, filed with `work/webrender-lcd-text-20261116`.

## Context

Chrome 159 renders text of 48 device px or less with LCD subpixel antialiasing
(Skia LCD16). The owner decided on 2026-11-16 to implement LCD text in Simple
rather than disable it in Chrome. The CPU lanes (`cpu`, `cpu_simd`, `software`)
now do this:

- The rasterizer is `sfnt_render_glyph_lcd` (`src/lib/common/encoding/sfnt_glyf.spl`).
- An atlas cell becomes `(avg << 24) | (r << 16) | (g << 8) | b`. A grayscale
  cell keeps `rgb = 0xFFFFFF`.
- The composite is `engine2d_lcd_quad_composite` (`engine2d/engine.spl`). It
  blends per channel, Skia blend_lcd16 style.
- The spec is `test/01_unit/browser_engine/lcd_subpixel_text_chrome159_spec.spl`.

`Engine2D._lcd_text_active()` keeps LCD off on every other backend, so Vulkan
still renders grayscale text. It does not render wrong text.

## Why Vulkan is not a one-line change

1. **The kernel reads one coverage value per cell.** The packed font batch
   SPIR-V (`backend_vulkan_font_spirv.spl`, semantics version 2) and the
   OpenCL/CUDA/Metal twins in `common/gpu/font_atlas_composite.spl` all compute
   `mask_a = atlas[si] >> 24` and do a single-alpha "over" blend. An LCD cell
   needs three coverages: `cr/cg/cb = (atlas >> 16|8|0) & 255` when
   The CPU composite also maps each coverage through a per-text-colour-channel
   preblend table (`_engine2d_lcd_preblend`, `cov^(1 - 0.22*L/255)`). A kernel
   needs the same three 256-entry tables, or the `math_pow` inline.
   Quarter-pixel phase glyphs are ordinary extra atlas cells (glyph_index
   `-1 - phase`), so they need no kernel change.
   `atlas & 0xFFFFFF != 0xFFFFFF`. It also needs the per-channel mix
   `d + (((src - d) * s32) >> 5)`, with `s32 = s5 + (s5 >> 4)` and
   `s5 = (cov * color_a / 255) >> 3`.
   - These kernels already read `dst[di]` and write it back, so no
     dual-source blending is needed. The change is local to the kernel body.
2. **The GLSL source is not in the tree.** `backend_vulkan_font_spirv.spl` keeps
   only the words plus `Source SHA-256: 8a5c5422…`. There is no
   `shaders/*.comp` for it (compare the `rect_batch`, `blur_rect`,
   `shadow_rect` and `glass_material` lanes). Regenerating it needs that source
   recovered or rewritten first. The new blob also needs a
   `check-*-spirv-pinned.shs` row, like its siblings, and a semantics-version
   bump.
3. **The fallback cannot be per glyph.** Running LCD text on Vulkan through
   the CPU composite would need `read_pixels_region` per glyph quad. On Vulkan
   that is a pending-compute flush plus a whole-frame readback per quad
   (`Engine2D.read_pixels_region`). That cost is why `_lcd_text_active()`
   excludes it.

## Fix plan

- Recover or rewrite the font batch GLSL as `shaders/font_atlas_batch.comp`.
- Add the per-channel branch.
- Regenerate the SPIR-V, bump `FONT_ATLAS_COMPOSITE_VULKAN_SEMANTICS_VERSION`, and
  add the pinned-SPIR-V check.
- Let `_lcd_text_active()` admit `vulkan`.
- Acceptance: the spec above, run with the backend `vulkan` (llvmpipe), paints
  the same stem bytes as `cpu_simd`.
