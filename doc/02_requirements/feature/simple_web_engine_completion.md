# Feature Requirements: Simple Web Engine Completion (`release/1.0.0`)

- **Date:** 2026-11-28
- **Status:** Approved by User (Option B)
- **Target Branch:** `release/1.0.0` (never `main`)
- **Worktree:** `/Users/ormastes/work/web_2d_gui` (`work/web-engine-complete`)
- **Research Links:**
  - [Local Research](../../01_research/local/simple_web_engine_completion_2026_11.md)
  - [Domain Research](../../01_research/domain/simple_web_engine_completion_2026_11.md)

## Selected Scope: Full Web Engine + Interactive Browser Completion on `release/1.0.0`

| ID | Requirement | Target Area | Priority |
|---|---|---|---|
| `REQ-WEB-001` | Paint non-positioned float subtrees after normal-flow block backgrounds and before inline content per CSS 2.2 Appendix E (both Draw IR `_html_draw_ir_node_paint_order` and raster `_paint_passes`). | `paint_layout.spl`, `paint_raster.spl` | P2 |
| `REQ-WEB-002` | Size `grid-template-columns: auto ...` tracks holding `display:flex` (or wrapped flex) children using true max-content width with intrinsic `%` margins resolved to `0`. | `layout_engine.spl` | P2 |
| `REQ-WEB-003` | Apply consistent `LayoutUnit` (`1/64` px) ceiling in `inline_item_width_err_milli` over exact unit sums, unify `plain_button_item` / `flex_row_button_label_at_edge` gates, shape `<input type=button|submit|reset>` at device scale `k`, and enforce `FORM_CONTROL_MEASURE_MAX_PX`. | `layout_foundation.spl`, `layout_engine.spl` | P3 |
| `REQ-WEB-004` | Close measurable fractional layout follow-ups (`top`/`bottom` baseline at `k=4`, `hangs_from_baseline` for `inline-block`, `clear` vs `margin-top`, SVG edge AA & post-clamp residual). | `layout_engine.spl`, `paint_draw_ir.spl` | P3 |
| `REQ-WEB-005` | Interactive `simple browser --open` pointer hit-testing (`<a href>` click navigation, `<button>` action dispatch, hover cursor/status), wheel scroll with clamped `scroll_y`, and keyboard navigation (Reload, Back/Forward history, Close) with rendering kept in `main.spl`. | `src/app/browser/main.spl`, `gui_window.spl`, `render_adapter.spl` | P2 |
| `REQ-WEB-006` | Single backend resolver authority (`simple_web_renderer.spl` <-> `render_lane.spl`) with fail-closed `vulkan`/`software`/`cpu` provenance receipts and `material_fallback` preservation. | `render_lane.spl`, `simple_web_renderer.spl`, `web_render_pixel_backend.spl` | P2 |
| `REQ-WEB-007` | System & unit SSpec suite (`test/01_unit/browser_engine/`, `test/03_system/app/browser/`) with real pixel/geometry/interaction assertions, no placeholders, and synced `doc/06_spec/` manuals (`0` `.spl` files under `doc/06_spec`). | `test/**`, `doc/06_spec/**` | P2 |
| `REQ-WEB-008` | Preserve pinned regression gates (`check-simple-web-engine2d-js-bitmap-evidence.shs` `mismatch_count=0`, `check-widget-shells-crossengine-evidence.shs` `>= 80%` Chrome/Electron non-text agreement on macOS). | `scripts/check/`, `browser_engine/` | P1 |

## Delivery Slices (Interactive Foreground)
1. **Slice 1 (Current):** `REQ-WEB-001` (CSS 2.2 float stacking order) + `REQ-WEB-002` (Grid `auto` track with flex child).
2. **Slice 2:** `REQ-WEB-003` + `REQ-WEB-004` (Inline `LayoutUnit` `1/64` px ceil, flex/inline/input button device precision, fractional follow-ups).
3. **Slice 3:** `REQ-WEB-005` + `REQ-WEB-006` + `REQ-WEB-007` + `REQ-WEB-008` (Interactive `simple browser --open` event loop + resolver/provenance + SSpec & cross-engine parity verification).
