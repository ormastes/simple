# Detail Design: Unified CSS & Simple UI Layout Refactor

**Date:** 2026-11-28
**Worktree:** `/Users/ormastes/work/carbon_chrome_layout`
**Architecture:** `doc/04_architecture/unified_css_and_ui_layout_refactor.md`

---

## 1. Shared Primitives (`src/lib/common/layout/constraint_space.spl`)

### 1.1 Data Structures

```simple
val LAYOUT_UNIT_CELLS: i32 = 0
val LAYOUT_UNIT_PIXELS: i32 = 1

struct EdgeInsets:
    top: i32
    right: i32
    bottom: i32
    left: i32

struct GapSpacing:
    row_gap: i32
    col_gap: i32

struct MinMaxSizes:
    min_content: i32
    max_content: i32

struct LayoutBounds:
    x: i32
    y: i32
    w: i32
    h: i32

struct ConstraintSpace:
    available_w: i32
    available_h: i32
    percent_base_w: i32
    percent_base_h: i32
    is_fixed_w: bool
    is_fixed_h: bool
    is_shrink_to_fit: bool
    unit_mode: i32
    scale_permille: i32
    min_w: i32
    max_w: i32
    min_h: i32
    max_h: i32

struct AxisTrackSpec:
    fixed_size: i32        # >0 when fixed or definite flex-basis; 0 for flex/auto
    flex_grow: i32         # grow weight (>= 0)
    flex_shrink: i32       # shrink weight (>= 0)
    min_size: i32          # floor (0 = none)
    max_size: i32          # cap (0 = none)
    intrinsic_max: i32     # auto max-content hint when fixed_size == 0 and flex_grow == 0
    margin_before: i32
    margin_after: i32
    margin_before_auto: bool
    margin_after_auto: bool

struct AxisSlot:
    offset: i32
    size: i32
    margin_before: i32
    margin_after: i32
    clamped_min: bool
    clamped_max: bool
```

### 1.2 Shared Algorithms
1. **`clamp_span(value: i32, min_val: i32, max_val: i32) -> i32`:**
   - Applies `if max_val > 0 and out > max_val: out = max_val`, then `if min_val > 0 and out < min_val: out = min_val` (`min` beats `max`), matching `clamp_dim` and CSS 2.1 §10.4.
2. **`MinMaxSizes.shrink_to_fit(available: i32) -> i32`:**
   - Computes `min(max(min_content, available), max_content)` when `max_content > 0`.
3. **`EdgeInsets.inset_bounds(x: i32, y: i32, w: i32, h: i32) -> LayoutBounds`:**
   - Computes `x + left`, `y + top`, `max(0, w - left - right)`, `max(0, h - top - bottom)`.
4. **`GapSpacing.total_gap(count: i32, gap: i32) -> i32`:**
   - Returns `(count - 1) * gap` if `count > 1 and gap > 0`, else `0`.
5. **`axis_distribute(available: i32, gap: i32, justify: text, specs: [AxisTrackSpec], last_remainder_mode: bool) -> [AxisSlot]`:**
   - Step 1: Resolve total fixed base + margins + gaps (`total_gap`).
   - Step 2:
     - When `last_remainder_mode == true` (Simple UI widget contract):
       - Reserve fixed items (`fixed_size > 0`), remaining space `flex_avail = max(0, available - fixed_total - total_gap - margins)`.
       - `flex_unit = flex_avail / total_flex`, `flex_remainder = flex_avail % total_flex`.
       - Award `flex_unit * spec.flex_grow + (if is_last_positive_flex: flex_remainder else: 0)`, then clamp with `clamp_span(size, spec.min_size, spec.max_size)`.
     - When `last_remainder_mode == false` (CSS Flexbox §9.7 solver):
       - Measure base sizes (using `fixed_size` or `intrinsic_max`).
       - If `free > 0` and `total_grow > 0`: iterative freeze loop for min-floor (`min_size`) and max-cap (`max_size`) violations, assigning cumulative rounded shares (`free * acc_after / total - free * acc_before / total`).
       - If `free < 0` and `total_shrink_weight > 0`: iterative freeze loop for `min_size` floor violations using `flex_shrink * base_size`, distributing exact deficit across remaining unfrozen shrinkable items.
       - If `free > 0` and no grow consumed it: distribute remaining free space to `margin_before_auto` / `margin_after_auto`, or `justify-content` (`flex-start`, `center`, `flex-end`, `space-between`, `space-around`, `space-evenly`).
   - Step 3: Place slots sequentially: `cursor += resolved_margin_before`, record `slot`, `cursor += slot.size + resolved_margin_after + gap + justify_extra`.

---

## 2. Simple UI Widget Layout Refactor (`src/lib/common/ui/layout.spl`)

1. **Deduplicate `layout_vbox` & `layout_hbox`:**
   - Extract `_layout_axis_children(children: [WidgetNode], space: ConstraintSpace, spacing: GapSpacing, horizontal: bool) -> [WidgetRect]` backed by `axis_distribute(..., last_remainder_mode: true)`.
   - `layout_vbox(...)` and `layout_hbox(...)` keep their exact legacy signatures and delegate to `_layout_axis_children`.
2. **Padding & Gap Support (`_layout_scaled`, `_layout_axis_children`, `layout_grid`):**
   - Parse integer `"padding"` (supports single `"8"` or CSS-style `"top right bottom left"` / `"v h"`), scaled via `_apply_scale(..., scale_permille)`.
   - Parse `"gap"` (and `"row_gap"` / `"column_gap"` overrides) on containers, scaled once via `_apply_scale(..., scale_permille)`.
   - Apply container border/title inset first (preserving `PIXEL_PANEL_TITLE_HEIGHT` and 1px panel border contract), then `EdgeInsets.inset_bounds(...)` for `"padding"`.
3. **Grid Track Upgrade (`layout_grid`):**
   - Subtract `total_col_gap = GapSpacing.total_gap(cols, col_gap)` and `total_row_gap = GapSpacing.total_gap(rows, row_gap)` before computing track base & single-remainder allocation via `axis_distribute`, keeping last column right-aligned to inner right edge and last row bottom-aligned to inner bottom edge.
4. **Unit-Mode Explicitness (`UiConstraintSpace`):**
   - `compute_layout` constructs a `ConstraintSpace` with `unit_mode = LAYOUT_UNIT_CELLS` (unless `panel_title_height > 0`, which indicates pixel mode); `compute_pixel_layout` uses `LAYOUT_UNIT_PIXELS` + `PIXEL_PANEL_TITLE_HEIGHT`.
   - Fixed widget defaults honor unit mode (keeping all existing `widget_draw_ir_panel_title_spec` and `layout_scale_spec` pixel expectations invariant).

---

## 3. CSS Layout & Draw IR Fixes (`browser_engine`)

### 3.1 `CssConstraintSpace` & `MinMaxSizes` Integration (`layout_foundation.spl`, `layout_text.spl`, `layout_engine.spl`)
- Add `CssConstraintSpace` builder helpers wrapping `ConstraintSpace` & `MinMaxSizes` (`css_constraint_space`, `css_flex_shrink_distribute` / `css_flex_row_measure_item`) in `layout_foundation.spl`.

### 3.2 Flexbox Fixes (`layout_engine.spl` & `layout_text.spl`)
1. **Auto-width shrink + min-width freeze (`layout_engine.spl:3636-4015`):**
   - Remove `(cst.width_px != 0 or cst.flex_basis_px > 0)` restriction at `L3922`: include auto-width / auto-basis items (`intrinsic_w > 0`) in shrink computation (`base_w = intrinsic_w`).
   - Run an explicit CSS §9.7 shrink-freeze pre-pass when `shrink_deficit > 0 and shrink_scaled_total > 0`, freezing any item whose shrunk width falls below its `min-width: auto` floor (`flex_item_min_content_w` or explicit `min_width_px`, or `frame_w` when `overflow: hidden/auto/scroll`) and redistributing the remaining deficit across non-frozen shrinkable items.
2. **`row_flex_item_auto_intrinsic_w` (`layout_engine.spl:885-901`) & `_lay_flex_item_max_content_width_inner` (`layout_text.spl:884-885`):**
   - Always apply `constrained_outer_width(node, st, ...)` to intrinsic flex width (so `min-width`/`max-width` apply even with zero margins/padding).
   - Compare `intrinsic_text_width + margins` against `flex_item_max_content_width` when the flex item contains block/non-inline descendants so wide block children aren't ignored!
   - Fix `layout_text.spl:884` to use `css_outer_width(nodes[c], cst, cst.width_px)` instead of blindly adding padding/border on `border-box` elements.
3. **`%`-width fallback (`layout_engine.spl:3997`):**
   - Replace `remaining_w = iw` when `cst.width_px < 0` with `flex_item_authored_outer_w(nodes[fc], cst, iw)`.
4. **Wrapping row `flex-grow > 0` with `flex-basis: auto` (`layout_engine.spl:3222`, `layout_text.spl:981-988`):**
   - When `cst.flex_basis_px == 0 and not cst.flex_basis_zero and cst.width_px == 0`, allow `flex_wrap_auto_base_width` to measure `flex_item_max_content_width` (capped at `iw`) even when `cst.flex_grow != 0` (`flex: 1 1 auto`), while preserving zero-basis (`flex: 1`) behavior!

### 3.3 Inline & `inline-block` Wrapping & Advance (`layout_engine.spl:5139-5320`)
1. Change `L5310` guard from `inline_x > 0` to `inline_x > inline_start_x` so float-shortened lines don't spuriously break before their first item.
2. Detect atomic/non-splittable inline elements (`inline_atomic_span`: `display: inline` with non-zero horizontal `pad`/`border` or `white_space_nowrap` and `child_count > 0` / text child) and wrap before placing them when `inline_x > inline_start_x and inline_x + inline_outer_w > line_iw`.
3. Ensure `out_bw[c]` on inline padded boxes retains `inline_w` including padding/border so `inline_x` advances accurately past badges/pills without overlapping adjacent text.

### 3.4 Grid Omitted Template Columns & Table Auto Fallback (`layout_engine.spl`, `layout_foundation.spl`)
1. **CSS Grid without `grid-template-columns` (`layout_engine.spl:2792-2804`):**
   - When `st.display == "grid"` and `grid_template_columns == ""`:
     - If `grid_extents[0] > 1` or `grid_auto_columns != ""` or `grid_auto_flow_column`, size explicit+implicit tracks via `grid_column_sizes_with_implicit`.
     - Otherwise enter Grid layout with `1` implicit column (`grid_auto_template_n = 1` or 1 implicit track sized `auto` -> stretched to `iw` under default `justify-content: normal`), preventing block-flow fallthrough and preserving `gap`, non-collapsing margins, and `grid-template-rows`.
2. **Table auto layout with `colspan` / `min-width` / `max-width` under `border-collapse` (`layout_foundation.spl:2868-2873`, `layout_engine.spl:2543-2745`):**
   - Lift the bailout at `layout_foundation.spl:2868` when `span > 1` or `min_width_px`/`max_width_px` is set: distribute single-column min/max widths first, expand spanned columns only for deficits across their spanned columns (CSS 2.1 §17.5.2.2), and enter table layout at `layout_engine.spl:2543` whenever `st.display == "table"` and `table_rows.rows.len() > 0` (even if `table_spacing_x == 0`), keeping all `<td>`/`<th>` horizontal instead of collapsing into block flow!
   - Also record `<thead>`/`<tbody>`/`<tfoot>` heights accurately including trailing collapsed border where applicable and initializing empty row groups to `0`.

### 3.5 Draw IR Scrollable Document Visibility & Clipping (`paint_layout.spl`)
- In `_html_draw_ir_visible_nodes` and `_html_draw_ir_commands`:
  - Keep `clip_cache` passed from `_simple_web_layout_compose_retained` (preserving 100% compliance with `web_draw_ir_clip_cache_contract_spec.spl`).
  - Determine which nodes have a *real* ancestor `overflow` / `textarea` clip (`node_has_scrollport_clip`) vs only root `clip_cache.default_clip`.
  - Compute the scrollable document bottom `doc_bottom_y = max(default_clip.y1, max_box_bottom)`.
  - For retained Draw IR visibility (`_html_draw_ir_visible`), relax `default_clip.y1` downward to `doc_bottom_y` so below-the-fold (`y >= viewport_h`) elements are NOT silently dropped from Draw IR (`Bug 0`), while:
    1. Still culling scrolled-off nodes completely above the top edge (`y1 <= clip.y0` when `clip.y0 == 0` and box/shadow ends above `0`, OR Wait — check: if `scroll_y > 0`, scrolled-off top boxes have `y1 <= 0` so raster doesn't overpaint negative `y`, whereas at `scroll_y == 0` all document boxes `[0 .. doc_bottom_y)` stay visible!).
    2. For a node inside an ancestor `overflow: hidden | auto | scroll` or `textarea` below `viewport_h`, compute its real ancestor clip directly against `(0, 0, default_clip.x1, doc_bottom_y)` instead of letting `default_clip.y1` invert the `overflow` clip rectangle!
    3. Keep all in-viewport `overflow` clip coordinates bit-identical (so `web_draw_ir_clip_cache_contract_spec`, `input_text_overflow_clip_chrome159_spec`, and `clip_device_offset_owner_chrome159_spec` remain unchanged).
