# Architecture: Simple Web Engine Completion (`release/1.0.0`)

- **Date:** 2026-11-28
- **Status:** Design Review (Step 2)
- **Target Branch:** `release/1.0.0`
- **Requirements:** [Feature](../../02_requirements/feature/simple_web_engine_completion.md), [NFR](../../02_requirements/nfr/simple_web_engine_completion.md)
- **Knowledge Route:** `rendering_ui` -> `browser_engine` / `ui_render` / `web_render_css_parity` / `browser`

## 1. Pipeline & Layering Boundaries
Simple Web Engine preserves the single canonical pipeline and avoids introducing parallel IRs:
```
HTML / CSS / JS  -->  DOM + Cascade + Layout (browser_engine)
                           |
           +---------------+---------------+
           |                               |
   DrawIR-v3 (Engine2D)             Software Raster (_paint_passes)
   paint_layout.spl -> draw_ir_adv  paint_raster.spl -> Engine2D readback
           |                               |
           +---------------+---------------+
                           v
           Single Backend Resolver (simple_web_renderer.spl / render_lane.spl)
                           v
           Hosted Window Loop (src/app/browser/main.spl -> gui_window.spl -> GuiRenderer)
```

### Key Architectural Invariants
1. **CSS 2.2 Appendix E Stacking Context Parity Across Both Paint Lanes (`REQ-WEB-001`):**
   - Both Draw IR (`_html_draw_ir_node_paint_order` in `paint_layout.spl`) and Software Raster (`_paint_passes` in `paint_raster.spl`) must enforce the same stacking phase order within each stacking context:
     - Phase A (Step 3/4): Non-positioned, non-float normal-flow block boxes (`float_mode == 0`).
     - Phase B (Step 5): Non-positioned float roots and their non-context-opening descendants (`in_float_subtree`).
     - Phase C (Step 7): In-flow inline-level / text content (`#text` and inline boxes outside float subtrees), then deferred context outlines.
     - Phase D/E: Relative/z=0 positioned contexts, then positive `z-index` contexts.
   - Opacity/backdrop groups remain contiguous over their `owner_nodes` subtrees (`opacity_pct < 100` ancestors are kept coherent via context/group placement).
2. **Intrinsic Sizing Isolation (`REQ-WEB-002`):**
   - CSS Grid `auto` track max-content resolution (`grid_explicit_auto_column_sizes` -> `row_flex_item_auto_intrinsic_w`) evaluates intrinsic widths with `%` margins resolved to `0` (`iw = 0` for percentage margin resolution), preventing `available_w` bleed into direct `display:flex` grid items as well as wrapped flex containers.
3. **Device-Scale `LayoutUnit` & Control Precision (`REQ-WEB-003`, `REQ-WEB-004`):**
   - Inline items (`inline_item_width_err_milli`) compute widths over exact font unit sums and apply one `layout_unit_ceil_milli` (`1/64` px) boundary at the item level (including single-edge-space items), aligned with unified `plain_button_item` / `flex_row_button_label_at_edge` gates and `FORM_CONTROL_MEASURE_MAX_PX`-capped `<button>` / `<input type=button|submit|reset>` shaping.
4. **JIT-Safe Browser Event Loop Boundary (`REQ-WEB-005`, `NFR-WEB-004`):**
   - `src/app/browser/gui_window.spl` remains a pure OS-window event & pixel-blit adapter (`GuiRenderer`).
   - All `browser_engine_frame_at` renders, scroll re-renders, hit-test dispatch, and URL navigation stay in `src/app/browser/main.spl` (`browser_open_window`) to prevent the silent whole-module tree-walk interpreter fallback documented in `gui_window.spl`.
5. **Single Backend Resolver Authority (`REQ-WEB-006`):**
   - Backend selection flows once through `simple_web_engine2d_resolved_backend_name` (`simple_web_renderer.spl`) and `browser_render_html_frame` (`render_lane.spl`), emitting fail-closed `"vulkan"` / `"software"` / `"cpu"` receipts.
