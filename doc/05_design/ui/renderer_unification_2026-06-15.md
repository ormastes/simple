<!-- codex-design -->
# Renderer Unification: common / web / text renderers on one 2D API

- **Date:** 2026-06-15
- **Status:** realized (incremental; see "Landed" below)
- **Area:** `lib/common/render_scene`, `lib/common/text_layout`,
  `lib/gc_async_mut/gpu/engine2d`, `lib/gc_async_mut/gpu/browser_engine`,
  `lib/editor/render`, `app/office`

## Goal

One 2D API, selected by config/environment, with three renderers sharing a
common base and **no duplication of the cheap shared logic**:

- **common renderer** — the dependency-free shared base (style cascade + layout
  primitives) in `lib/common/render_scene` and `lib/common/ui/draw_ir`.
- **web renderer** — HTML → CSS cascade → block layout → paint over Engine2D
  (`browser_engine/simple_web_renderer.spl`).
- **text renderer (TUI)** — a *slim* component that shares the cascade and can
  optionally offload to the same GPU draw-IR lane as the GUI.

## Key facts that shaped the design (audit, 2026-06-15)

- The **2D backend is already unified**: a single `RenderBackend` trait
  (`nogc_async_mut/gpu/engine2d/backend.spl`) is implemented by every lane —
  SIMD CPU (`backend_cpu`), `software`, and all GPU backends (cuda/vulkan/metal/
  rocm/intel/opencl/opengl/webgpu/…). `Engine2D` is the facade.
- Selection was **hardcoded** (priority probe + explicit name) — there was no
  config/env knob. (Added; see below.)
- The TUI markdown renderer (`editor/render/md_renderer.spl`) was a *third*,
  fully separate cascade (hardcoded ANSI literals), with zero gpu imports — slim,
  but duplicative of the style decisions.
- `office_style_resolver` already had the dual projection
  `style_to_css_text` (HTML) / `style_to_sgr` (TUI) from one `resolve_style` —
  the natural common-cascade seam.

## Decisions

1. **Share the interface, don't rewrite the APIs.** "Minimize duplication" =
   share the cheap cascade (`office_style_resolver`), the draw-IR
   (`common.ui.draw_ir`), and the **backend interface** (`RenderBackend` /
   `Engine2D`). The other 2D APIs (game2d, skia, drawing/compositor) keep their
   own rich draw surfaces but gain **additive bridges** that dispatch their
   primitives onto the shared SIMD-CPU/GPU lanes — so they share the
   SIMD-CPU/GPU interface without a risky merge of distinct surfaces. Do **not**
   relocate the ~5100-line `simple_web_html_layout_renderer` layout half into
   `common` (that one IS deferred).
2. **Config/env backend selection.** `Engine2D.detect_best_backend()` honors
   `SIMPLE_2D_BACKEND` (e.g. `cpu_simd`, `software`, `cuda`, `vulkan`) when the
   named lane initializes; otherwise it auto-probes. Same API, env-selected lane.
3. **TUI stays slim by default; GPU is opt-in.** `md_renderer.spl` keeps zero
   gpu imports and now derives heading/code/quote *style* from the shared
   cascade (`style_to_sgr(resolve_style(tag,[]))`). A **separate** opt-in module
   `editor/render/md_draw_ir.spl` projects the rendered TUI lines into a
   `DrawIrComposition` of TEXT commands — the same IR the GUI dispatches to GPU
   backends — so the TUI "lane" is GPU-offloadable like the GUI without making
   the default path heavier.
4. **CPU owns glyph rasterization; supported GPU lanes compose the atlas.**
   Legacy checksum payloads are not native rasterization evidence. CPU
   composition remains load-bearing, and transparency/alpha coverage still
   uses an absolute oracle.
5. **Unspecified text follows the font-provider candidate policy.** The
   zero-config Engine2D path remains backend bitmap text; vector faces are
   opt-in. Explicit families use the same provider rather than a GUI-local
   default.
6. **MD WYSIWYG is wired end-to-end.** `app/office/md_wysiwyg_ppm.spl` (headless
   PPM) and `md_wysiwyg_gui.spl` (window) feed `wysiwyg_preview_pane` HTML
   through `simple_web_render_html_to_pixels_with_engine2d_backend`.

## Landed (2026-06-15)

- Bitmap GPU-offload parity + `common.text_layout` facade (fixes the previously
  100%-failing `font_renderer_spec`).
- Fira default (glyph + HTML seams), `office_style_resolver` font-family.
- MD WYSIWYG render apps (ppm + gui) + pixel-oracle sanity spec.
- Markdown heading crash fix (chained `.slice` on a text temporary).
- `SIMPLE_2D_BACKEND` env/config backend selection + transparency spec.
- TUI shared cascade + opt-in `md_draw_ir` GPU projection.
- **Other 2D APIs share the SIMD-CPU/GPU interface via additive bridges:**
  `engine2d/bridge_game2d.spl`, `skia/bridge/engine2d_bridge.spl`,
  `engine2d/bridge_drawing_compositor.spl`. Each has a pixel-oracle spec proving
  its primitives paint through the shared `Engine2D` `cpu_simd` AND `software`
  lanes. Unmapped primitives (game2d DrawTriangles; skia DrawRRect/Path/TextBlob;
  compositor non-Normal blend modes) are counted/TODO'd, never silently dropped.

## Not done / follow-ups

- `text_metrics_spec` + `layout_text_node_spec` are orphaned against a deleted
  style-based browser_engine layout API (see bug
  `text_metrics_spec_orphaned_browser_engine_api_2026-06-15`). Needs an
  API-restoration or spec-reauthor decision, out of this iteration's scope.
- Relocating the web layout engine into `common` is explicitly deferred
  (over-engineering risk). The bridges cover the core primitives; full primitive
  coverage (paths, rrects, text blobs, all blend modes, sprite-texture blits) is
  incremental follow-up.
