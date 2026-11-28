# Local Research: Simple Web Engine Completion on `release/1.0.0` (2026-11)

- **Date:** 2026-11-28
- **Target Branch:** `release/1.0.0` (never `main`)
- **Worktree:** `/Users/ormastes/work/web_2d_gui` (`work/web-engine-complete` off `origin/release/1.0.0` `7b061292f90`)
- **Sidecar Status:** `N/A` for Web Engine (handled interactively in foreground; sibling lanes `Simple 2D` and `Simple GUI` executed via dedicated `self` subagents in separate worktrees).

## Knowledge Route Receipt
Resolved from `doc/00_llm_process/knowledge_registry.sdn`:
- **Prefix route:** `src/lib/gc_async_mut/gpu/browser_engine` -> `group_id: rendering_ui` ([doc/00_llm_process/feature_group/rendering_ui/skill.md](../../00_llm_process/feature_group/rendering_ui/skill.md))
- **Layer expert:** [doc/00_llm_process/layer_expert/browser_engine/skill.md](../../00_llm_process/layer_expert/browser_engine/skill.md) & [doc/00_llm_process/layer_expert/ui_render/skill.md](../../00_llm_process/layer_expert/ui_render/skill.md)
- **Feature experts:** [doc/00_llm_process/feature_expert/web_render_css_parity/skill.md](../../00_llm_process/feature_expert/web_render_css_parity/skill.md) & [doc/00_llm_process/feature_expert/browser/skill.md](../../00_llm_process/feature_expert/browser/skill.md)
- **Shared render contract:** `DrawIrV3Scene` / `Engine2D`, preserving `mismatch_count=0` on `check-simple-web-engine2d-js-bitmap-evidence.shs`.

## Prior Work Already Landed on `release/1.0.0` (Do Not Re-Implement)
1. **Radial gradients & multi-layer background stacks:** `radial_gradient_geometry_q10`, `fb_background_radial_stack_clip` (`simple_web_html_layout_renderer_paint_primitives.spl:1280, 1467`), and `fb_gradient_layers_clip` (`paint_raster.spl:1420-1441`), plus Vulkan `gradient_layer.comp`.
2. **Backdrop-filter blur & color matrices:** `_paint_backdrop_blur` (`paint_raster.spl:145-165`), `_simple_web_backdrop_root_split` (`simple_web_html_layout_renderer.spl:523`), and `engine2d_backdrop_blur_pixels` (`draw_ir_adv.spl:1325`).
3. **Grid fractional `fr` & `grid-area` implicit tracks (`w4-2`):** fixed in `_declarations.spl` and `_layout_engine.spl`.
4. **4x `background-clip: content-box` (`W6-2`):** fixed in `draw_ir_adv.spl:1160-1315`.
5. **Fractional `min-width` (`w5-5`):** `Style.min_width_milli` landed across `style.spl`, `declarations.spl`, `layout_foundation.spl`, and `layout_engine.spl`.
6. **Backend resolver unification (`W4-5`):** `simple_web_renderer.spl:55` aliases `simple_web_engine2d_resolved_backend_name` and `_simple_web_engine2d_render_html_pixels_resolved` resolves once per render.

## Verified Open Gaps & Root Causes

### Pillar W1 — CSS 2.2 Appendix E Stacking Order (Floats vs Later Block Backgrounds)
- **Bug:** `doc/08_tracking/bug/db/web_render_float_painted_under_later_block_background_2026-11-28.sdn` (`P2, open`)
- **Root cause:**
  - Draw IR path (`simple_web_html_layout_renderer_paint_layout.spl:759-782`, `_html_draw_ir_node_paint_order`): registers non-context nodes into `members[parent_context]` in flat document/tree order instead of separating Step 4 (non-positioned in-flow block backgrounds/borders) before Step 5 (non-positioned floats and their descendants) before Step 7 (inline content).
  - Software raster path (`simple_web_html_layout_renderer_paint_raster.spl:1390-1466`, `_paint_passes` Pass 1): paints `normal_flow` boxes in flat `0..node_count` document order, so a later `<div style="height:10px;background:#00aa00">` paints over an earlier `<div style="float:left;...">`.

### Pillar W2 — CSS Grid `auto` Track Intrinsic Sizing with Flex Child
- **Bug:** `doc/08_tracking/bug/db/web_grid_auto_track_takes_full_width_with_flex_item_2026-11-27.sdn` (`P3, fixing`)
- **Root cause:** `grid_explicit_auto_column_sizes` (`simple_web_html_layout_renderer_layout_engine.spl:1570`) calls `row_flex_item_auto_intrinsic_w(nodes, styles, child_index, c, cst, available_w, widths)`. Inside `row_flex_item_auto_intrinsic_w` (`L802-875`), when a grid item wraps a `display:flex` child (or directly has `display:flex` with `%` margins), `L856-857` resolves `%` margins against `available_w` (e.g., `205px`) instead of `0` for intrinsic max-content sizing, and block wrappers fall through to `intrinsic_text_width` instead of recursing into flex children.

### Pillar W3 — Inline Item `LayoutUnit` (1/64 px) & Button/Form-Control Device Precision
- **Bugs (all `P3, open`):**
  1. `web_render_inline_item_layoutunit_ceil_pen_2026-11-28.sdn` (`layout_foundation.spl:1836-1874`): `inline_item_width_err_milli` returns exact `base_width_milli` instead of `LayoutUnit::FromFloatCeil` (`1/64` px) over exact font unit sums, and edge-space branches ceil spaces separately from the text. Reproducer: `test/01_unit/browser_engine/inline_item_layoutunit_ceil_pen_chrome159_spec.spl` (`@tag:in-development`).
  2. `web_render_flex_button_device_width_gate_mismatch_2026-11-28.sdn` (`layout_engine.spl:4066`): `plain_button_item` only checks `tag == "button" and flex_wrap == "nowrap"`, diverging from `flex_row_button_label_at_edge` (`L1895`) and `box_device_extra_w` reset (`L6123`) which require `width_px <= 0 and flex_grow <= 0 and min_width_px <= 0 and min_width_milli <= 0`.
  3. `web_render_inline_button_label_whole_pen_2026-11-28.sdn` (`layout_engine.spl:5250, 5350`): inline (non-flex), row-reverse, wrapped, and `justify-content:center` auto-width `<button>` labels fall back to whole-px pens.
  4. `web_render_input_button_label_width_not_device_shaped_2026-11-28.sdn` (`layout_foundation.spl:1004`): `<input type=button|submit|reset>` does not route through `form_control_label_width_milli_px` at `k > 1`.
  5. `web_render_button_device_label_width_skips_measure_cap_2026-11-28.sdn` (`layout_foundation.spl:1026`): `k > 1` branch calls `resolve_font_metrics_with_language_milli` before bounding by `FORM_CONTROL_MEASURE_MAX_PX`.
  6. `web_render_fractional_layout_followups_2026-11-28.sdn` (`layout_engine.spl:2150`): 7 fractional follow-ups (`top`/`bottom` line device baseline, `inline-block` `hangs_from_baseline`, `clear` margin-top vs float bottom, partial SVG edge blending, `<br clear>`, post-clamp SVG residual, `middle` inline-block baseline).
- **Separate P2 Item (Optional):** `web_render_lcd_hinted_outline_not_freetype_exact_2026-11-28.sdn` (`src/lib/common/encoding/sfnt_glyf.spl:1473`) — full FreeType `af_latin` integer hinting port (note open 13/14 px skrifa vs FreeType oracle question).

### Pillar W4 — Interactive Hosted Browser Window (`src/app/browser/`)
- **Current state:** `browser_open_window` (`src/app/browser/main.spl:87-112`) + `browser_window_wait` (`src/app/browser/gui_window.spl:44-78`) only handle `GUI_EVT_CLOSE` and `GUI_EVT_RESIZED`. `GUI_EVT_MOUSE_BUTTON`, `GUI_EVT_MOUSE_MOVED`, `GUI_EVT_MOUSE_WHEEL`, and `GUI_EVT_KEYBOARD` (`src/lib/nogc_sync_mut/ui/gui_renderer.spl:75-78`) are dropped.
- **Load-bearing invariant:** Keep HTML rendering calls inside `main.spl` (not inside `gui_window.spl`), because moving engine calls into `gui_window.spl` triggers a silent tree-walk interpreter fallback (`browser_window_wait` docstring).
- **Missing interactive features:** link/button hit-testing (`DrawIrCommand.hit_rect` + `href`/action dispatch), vertical scroll (`scroll_y` clamped to document bottom + wheel delta), keyboard shortcuts (Reload, Back/Forward session history stack, Escape/Close), and optional JS/CSS animation frame loop integration (`run_browser_window_gui_frames`).

### Pillar W5 — macOS Parity & Evidence Verification (`release/1.0.0`)
- Confirm `check-simple-web-engine2d-js-bitmap-evidence.shs` (`mismatch_count=0`), `check-widget-shells-crossengine-evidence.shs` (`>= 80%` non-text Chrome/Electron parity), and Chrome-159 1x/4x layout/paint SSpec regressions on macOS `release/1.0.0`.
