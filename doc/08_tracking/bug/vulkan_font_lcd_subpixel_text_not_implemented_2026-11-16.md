# Vulkan font batch has no LCD subpixel text (CPU lanes do)

Status: FIXED 2026-11-17 on `work/vulkan-lcd-text-20261117` (see "Resolution" at the end; one decision left to the owner).
Was: OPEN 2026-11-16, filed with `work/webrender-lcd-text-20261116`.

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
2. **The GLSL source IS in the tree (corrected 2026-11-17).** It is
   `test/09_baselines/engine2d_vulkan/font_atlas_packed.comp`: its SHA-256 is
   exactly the `Source SHA-256: 8a5c5422…` recorded in
   `backend_vulkan_font_spirv.spl`. It lives with the baselines, not under
   `shaders/` like the `rect_batch`, `blur_rect`, `shadow_rect` and
   `glass_material` lanes, which is why the first search missed it.
   `glslangValidator` and `spirv-val` are installed in `~/.local/bin`, so
   this item does not block the fix. The new blob still needs a
   `check-*-spirv-pinned.shs` row, like its siblings, and a semantics-version
   bump.
3. **The fallback cannot be per glyph.** Running LCD text on Vulkan through
   the CPU composite would need `read_pixels_region` per glyph quad. On Vulkan
   that is a pending-compute flush plus a whole-frame readback per quad
   (`Engine2D.read_pixels_region`). That cost is why `_lcd_text_active()`
   excludes it.

## Fix plan

- Move `test/09_baselines/engine2d_vulkan/font_atlas_packed.comp` to `shaders/font_atlas_batch.comp` (or extend it in place), keeping its hash provenance.
- Add the per-channel branch.
- Regenerate the SPIR-V, bump `FONT_ATLAS_COMPOSITE_VULKAN_SEMANTICS_VERSION`, and
  add the pinned-SPIR-V check.
- Let `_lcd_text_active()` admit `vulkan`.
- Acceptance: the spec above, run with the backend `vulkan` (llvmpipe), paints
  the same stem bytes as `cpu_simd`.

## Resolution (2026-11-17)

The Vulkan packed font kernel now paints LCD subpixel text byte for byte like
`engine2d_lcd_quad_composite`, and `_lcd_text_active()` admits `vulkan`.

What changed:
- `shaders/font_atlas_batch.comp` is the shipping source (copied from
  `test/09_baselines/engine2d_vulkan/font_atlas_packed.comp`, which stays as the
  gray C-bench baseline). SPIR-V 7012 -> 12732 bytes, sha256
  `da1c8a82ce2ce822b80c27fa3e656d19ed7fa6272d94d2afb558364ac94ab9c5`
  (was `4b5f44e2...`), compiled with plain `glslangValidator -V`, `spirv-val` clean.
- `backend_vulkan_font_spirv.spl` regenerated (head + tail halves kept). Pinned by
  `scripts/check/check-font-atlas-batch-spirv-pinned.shs` (6-fixture selftest;
  also pins `# Source SHA-256` and the runtime-trusted sha), manifest row
  `push-font-atlas-batch-spirv-pinned` plus an exact dispatch arm in
  `check-push-must-pass.shs`, like the glass/blur/shadow siblings.
- Per-QUAD semantics, as on the CPU: LCD math only when the quad holds an LCD
  cell and every destination pixel is opaque and on the surface; otherwise the
  old gray blend for the whole quad. Inside an LCD quad gray cells go through the
  s32 tables too. The opacity gate needs a whole quad in one workgroup, so an LCD
  batch dispatches X = 1.
- Tables (`engine2d_lcd_s32_tables`, moved to `engine2d/helpers/lcd_s32_tables.spl`,
  not duplicated) and per-glyph indices ride in an opt-in trailer of the params
  buffer (header word 7 bit 31). Deviations from the plan, with reasons: the
  seed fixes the compute pipeline layout at bindings 0..2
  (`interpreter_extern/gpu.rs` ~5054), so there is no 4th storage binding; and
  the 7-word glyph record is unchanged because `metal_font_packed_parity_spec`
  and `VULKAN_FONT_PACKED_MAX_BYTES == 114720` pin it.
- Two traps found by differential runs against `cpu_simd`, both fixed and pinned:
  the 5x7 bitmap atlas has rgb = 0 (read as an LCD cell it blanks the text), and
  Draw IR's per-box clip trims quads on the host so a quad overhanging the
  surface looked fully on-surface to the kernel while the CPU, whose off-surface
  readback is 0, paints it gray (every page with text at x = 0 or flush right).

Evidence (lavapipe, `VK_DRIVER_FILES=/usr/share/vulkan/icd.d/lvp_icd.json`, seed
`cargo-target-webrender-vk`):
- `lcd_subpixel_text_chrome159_spec` AC-6/AC-7 were red on base (and still red
  with only `_lcd_text_active()` widened: 369 differing pixels on a probe page,
  `vector_font_device_executed=true`, so the kernel drew, not the CPU suffix) and
  are green; 7/7.
- `direction_rtl_bidi_order_chrome159_spec` AC-7 (LCD on, text flush at both
  surface edges) was red (87 px, all within 5 px of an edge) and is green; 7/7.
  AC-6 keeps `SIMPLE_WEB_LCD_TEXT=0`: its ink-order check is AA-sensitive like AC-5
  (it fails with LCD on although the frame equals the CPU frame).
- `vulkan_font_lcd_packed_params_spec` (new, 7 rows) pins the trailer layout.
- Differential probes (not committed, device frame vs `simple_web_render_html_to_pixels`
  at 64x64): 9 pages (edge-overhanging text, alpha text, text over a gradient and
  over a dark fill, 40 px and 11-12 px, overlapping glyphs, five text colours, a
  clip box) show 0 differing pixels; 7 of them ran on the device kernel, 2 (bottom
  edge, clip box) fell back to the CPU suffix and are not kernel evidence. The
  bitmap lane is covered by `input_password_mask_chrome159_spec` (5/5).
- Regression (head vs base, same failing names): `simple_web_renderer_spec`
  116/116, `browser_renderer_spec` 131/131 and 4/4, `web_device_scale_spec` 7/7,
  the six input/button chrome159 specs and the Vulkan engine2d font specs, apart
  from four specs that fail identically on base
  (`input_text_overlay_plan_contract_spec` 1, `backend_vulkan_font_perf_evidence_spec` 2,
  `backend_vulkan_font_spec` 5, `engine_vulkan_font_route_spec` 1). Wall time of
  `simple_web_renderer_spec` 149.8 / 147.6 s base vs 148.7 / 148.2 s head.

Left open:
1. `FONT_ATLAS_COMPOSITE_VULKAN_SEMANTICS_VERSION` is NOT bumped (still 2).
   `vulkan_session.spl:473` requires it to equal the common
   `FONT_ATLAS_COMPOSITE_SEMANTICS_VERSION`; bumping only the Vulkan one rejects
   every pinned install (`font-pipeline-semantics-mismatch`), and bumping the
   common one also hits the CUDA check (`backend_cuda_font_ptx.spl:182`,
   `engine.spl:1325`) and specs pinned at 2 (`font_atlas_composite_identity_spec`,
   `font_renderer_spec`, `cuda_generated_font_handoff_spec`). Owner decision.
2. The shipped kernel is now a superset of the frozen common GLSL
   (`font_atlas_composite_vulkan_glsl_source`, sha256 `8a5c5422...`, which
   `check-portable-compute-toolchains.shs` still compiles to `4b5f44e2...`). The
   `runtime-glsl` fallback (no pinned SPIR-V) keeps the legacy params layout and
   one-group-per-64-pixels grid (the packer is told `lcd = false` unless
   `artifact_mode == "precompiled-spirv"`; with the trailer and X = 1 it would
   have drawn only 64 pixels per glyph) and paints an LCD atlas cell as gray
   alpha, as do the OpenCL/CUDA/Metal twins, which `_lcd_text_active()` does not
   admit. Not exercised by a test (needs a no-SPIR-V install).
3. LCD on a trimmed quad gates on the visible pixels' opacity, the CPU on the
   whole untrimmed quad's; equal on an opaque frame, different on a translucent
   one (not exercised).
4. More than 32 distinct LCD text colours in one batch is refused and falls to
   the per-quad-readback CPU suffix (correct, slow).
5. Cost (lavapipe, 900x760, seed `cargo-target-webrender-vk`, three text pages,
   first / second render in one process, seconds). Base 16.2/6.8, 12.0/5.4, 6.7/5.4;
   head with `SIMPLE_WEB_LCD_TEXT=0` 16.5/7.1, 12.1/5.6, 6.9/5.5 (gray unchanged
   within ~5 %); head LCD on 61.6/10.8, 23.1/7.5, 13.4/7.5. LCD text is about 60 %
   slower steady and several times slower cold, the same order as the documented
   CPU LCD cost (+45-51 %); the share between LCD glyph raster, the host quad
   scan and the kernel was not profiled. The pooled params buffers grow from
   114,720 to 229,408 bytes per batch slot for every page, gray ones included.
6. Unexplained, flagged for review: peak RSS of `web_device_scale_spec` (and the
   probe above) is 1.1 GB on base and with `SIMPLE_WEB_LCD_TEXT=0`, but 246 MB on
   head with LCD on, with identical pixels (the specs pin exact bytes and ink
   counts). `simple_web_renderer_spec` shows the same 1.4 GB -> 246 MB with equal
   wall time. A 300k-call micro of `engine2d_lcd_s32_tables` moves 432 MB -> 297 MB
   when called from the new helper module instead of `engine.spl`, so the table
   cache living in the giant module is a suspect, not a proven cause.
7. The two "clip box" and "bottom edge" 64x64 probe pages report
   `vector_font_device_executed=false` with LCD on AND off, so that fallback to the
   CPU suffix is not caused by this change; at 900x760 the same constructs ran on
   the device on base and head.

## Follow-up (2026-11-19): one dispatch per overlapping LCD batch

Open item 5 (cost) is partly closed. The kernel now blends each chain of
overlapping quads inside one workgroup, so an LCD batch is one dispatch instead
of one per glyph of its longest word (text page: 456 -> 60 dispatches, byte
equal). The trailer word is now `chain length << 16 | table index`
(`0xFFFF` = no LCD), and the pinned SPIR-V sha256 is
`be8db6a0280107944e44e77fe37a4cf7140e982f411ba3dcee99138d77800075`.
Details and numbers: the "Chains" bullet of
`doc/00_llm_process/feature_expert/web_render_css_parity/skill.md`. What still
dominates Vulkan wall time is the atlas upload:
`vulkan_font_atlas_full_repack_interleaved_faces_2026-11-19.md`.
