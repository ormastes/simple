# Architecture: Unified CSS & Simple UI Layout Refactor

**Date:** 2026-11-28
**Worktree:** `/Users/ormastes/work/carbon_chrome_layout`
**Research Inputs:**
- `doc/01_research/domain/chrome_vs_simple_layout_algorithm.md`
- `doc/01_research/local/chrome_vs_simple_layout_diff.md`

---

## 1. Architectural Goal

Unify the core geometric math shared by **Simple UI widget layout** (`src/lib/common/ui/layout.spl`) and **Simple Web CSS layout** (`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout_*.spl`) under pure, dependency-leaf abstractions in `src/lib/common/layout/`, following Blink LayoutNG's separation of:

1. **Constraint Space (`ConstraintSpace`):** Immutable sizing inputs (`available_w/h`, `percent_base_w/h`, `is_fixed_w/h`, `is_shrink_to_fit`, `unit_mode`, `scale_permille`, min/max bounds).
2. **Intrinsic Sizing (`MinMaxSizes`):** Side-effect-free `(min_content, max_content)` bounds + CSS 2.1 shrink-to-fit (`min(max(min, available), max)`).
3. **Box Spacing (`GapSpacing`, `EdgeInsets`):** Uniform container inset subtraction (`padding`/`border`) and inter-item `gap` computation (`(count - 1) * gap`).
4. **Axis Distribution Solver (`AxisTrackSpec`, `AxisSlot`, `axis_distribute`):** Single shared linear track solver handling fixed sizes, flex-grow with max clamping & single remainder invariant, flex-shrink with min-floor freeze & redistribution, auto margins, and `justify-content` alignment.

---

## 2. Dependency Boundaries

```
src/lib/common/layout/                  <-- PURE LEAF (no DOM, no Style, no WidgetNode)
  ├── box_model.spl                     (BoxKind, BoxModel, BlockLayoutBox — preserved)
  ├── constraint_space.spl              (ConstraintSpace, MinMaxSizes, EdgeInsets,
  │                                      GapSpacing, AxisTrackSpec, AxisSlot, axis_distribute)
  ├── float_bands.spl                   (preserved)
  ├── margin_collapse.spl               (preserved)
  └── table_grid.spl                    (preserved)
          ^                                     ^
          |                                     |
src/lib/common/ui/layout.spl          src/lib/gc_async_mut/gpu/browser_engine/
  (UiConstraintSpace adapter;            simple_web_html_layout_renderer_layout_*.spl
   single _layout_axis_children;         (CssConstraintSpace adapter; Flex/Inline/Block/
   Cells vs Pixels unit mode;             Grid/Table fixes)
   gap & padding support)              + simple_web_html_layout_renderer_paint_layout.spl
                                         (Scrollable Draw IR visibility & overflow clip)
```

### Boundary Rules
- `src/lib/common/layout/**` MUST NOT import `common.ui.widget` or `std.gc_async_mut.gpu.browser_engine.*`.
- Existing public signatures of `common.layout.box_model` and `common.ui.layout` remain 100% intact for all callers (`widget_hit.spl`, `widget_draw_ir.spl`, `ui_gui_packed_producer.spl`, `layout_*_spec.spl`).
- In `browser_engine`, `simple_web_html_layout_renderer.spl`'s `build_ancestor_clip_cache` + `_html_draw_ir_visible_nodes` + `_html_draw_ir_commands` call contract pinned by `web_draw_ir_clip_cache_contract_spec.spl` is preserved; Draw IR visibility and clip handling for below-the-fold / scrolled content live cleanly inside `paint_layout.spl`.

---

## 3. Core Invariants

1. **Unit-Mode Separation in UI Layout:**
   - `LAYOUT_UNIT_CELLS` (terminal TUI `compute_layout`) preserves 1-cell borders, 0 title band (`panel_title_height == 0`), and 1-cell menubar/statusbar height.
   - `LAYOUT_UNIT_PIXELS` (`compute_pixel_layout`) carries DPI `scale_permille`, scaled `PIXEL_PANEL_TITLE_HEIGHT` (`18`), and scaled pixel `padding` & `gap`.
2. **UI Flex Remainder & Clamp Invariant:**
   - Exact preservation of `floor(avail / total_flex) * weight` + remainder awarded **at most once** to the last child with `flex > 0`.
   - `clamp_span(value, min_val, max_val)` applies `max` then `min` (`min` always wins when `min > max > 0`), and starved flex space clamps cleanly at `>= 0`.
3. **CSS Flexbox Overlap Prevention & Freeze Convergence:**
   - All shrinkable items (including auto-width items with `flex-shrink > 0`) participate in `shrink_deficit` redistribution, floored cleanly by `min-width` or `min-width: auto` (`min_content`), with frozen items removed cleanly so siblings never under-shrink or overlap.
   - `row_flex_item_auto_intrinsic_w` respects both inline content, block children (`flex_item_max_content_width`), `box-sizing: border-box`, and `min-width`/`max-width`.
4. **CSS Inline / `inline-block` Atomicity:**
   - Wrapping occurs only after a non-empty line segment (`inline_x > inline_start_x`) when an `inline-block`, replaced element, or unbreakable padded/nowrap `inline` span exceeds remaining line width (`line_iw - inline_x`).
5. **CSS Grid & Table Completeness (No Silent Block-Flow Drops):**
   - `display: grid` always runs Grid layout even without `grid-template-columns` (defaulting to implicit column placement from `grid-auto-columns: auto`).
   - `display: table` handles `colspan`, `min-width`, and `max-width` under `border-collapse: collapse` without falling back to vertical block stacking, and sizes `<thead>`/`<tbody>`/`<tfoot>` groups accurately.
6. **Draw IR Full-Document Scrollable Visibility (`Bug 0`):**
   - Retained Draw IR visibility (`_html_draw_ir_visible_nodes`) retains document-flow nodes beyond `viewport_h` (and keeps ancestor `overflow` clips un-inverted below `viewport_h`) while preserving viewport/scrollport clipping inside explicit `overflow` containers and `y1 <= 0` off-top scrolled regions cleanly.
