# Local Research: Chrome LayoutNG vs Simple UI & CSS Layout Diff

**Date:** 2026-11-28
**Worktree:** `/Users/ormastes/work/carbon_chrome_layout`
**Baseline Metrics Referenced:**
- `doc/10_metrics/ui/chrome_layout_geometry_diff_macos_2026-09-12.md`
- `doc/10_metrics/ui/chrome_vs_simple_catalog_diff_macos_2026-09-12.md`
- `doc/04_architecture/simple_web_engine_completion.md`

---

## 1. Simple UI Widget Layout (`src/lib/common/ui/layout.spl`) Diff

### 1.1 Architectural Gaps vs Constraint-Space Model
| Concern | Chrome / LayoutNG Model | Current `src/lib/common/ui/layout.spl` | Concrete Defect |
|---|---|---|---|
| **Axis Abstraction** | Single axis-parameterized solver with `ConstraintSpace` | `layout_vbox` (L153–221) and `layout_hbox` (L223–291) duplicate ~70 lines each | Bug fixes & remainder invariants must be updated twice; diverges over time |
| **Spacing & Padding** | `EdgeInsets` + `gap` subtracted prior to flex/track distribution | No container `"padding"` or `"gap"` lookup anywhere in `layout.spl` (despite `builder.spl:738` setting `"padding"`) | Containers ignore `padding` & `gap`; widgets pack edge-to-edge |
| **Intrinsic Sizing (`MinMaxSizes`)** | Bottom-up `min_content`/`max_content` | Unsized child defaults to `flex = 1`; fixed children never respect `min_*`/`max_*` before reserving space | Starved/overflowed rows either overflow container silently or zero out content widgets |
| **TUI Cells vs Pixels** | Explicit unit space in `ConstraintSpace` | `compute_layout` vs `compute_pixel_layout` differentiated only by `panel_title_height: i32 = 0` (`PIXEL_PANEL_TITLE_HEIGHT = 18`); `get_fixed_height` hardcodes `1` for `menubar`/`statusbar` | TUI column/row contracts leak into pixel surfaces (`SC_BAR_H=22` workarounds in `showcase_core.spl`) |
| **Grid Layout** | Explicit/implicit track sizing + gap + remainder | `layout_grid` (L300–386) splits `w` and `h` evenly without `gap`, `padding`, or track sizing | No gap support; nested border padding ignored |

---

## 2. Simple CSS Layout Engine (`browser_engine`) Diff

### 2.1 Bug 0: Draw IR Viewport Clip Silently Drops Below-the-Fold Commands
- **Evidence Observed:**
  - `simple_web_html_layout_renderer.spl:817-822` (`_simple_web_layout_compose_retained`) calls:
    ```simple
    val clip_cache = build_ancestor_clip_cache(
        nodes, paint_styles, boxes.bx, boxes.by, boxes.bw, boxes.bh, width, height
    )
    val visible_nodes = _html_draw_ir_visible_nodes(
        nodes, paint_styles, boxes, clip_cache
    )
    ```
  - `paint_raster.spl:401-405` sets `default_clip = ClipRect(x0: 0, y0: 0, x1: fbw, y1: fbh)`, and intersects every clipping ancestor with `default_clip`.
  - `paint_layout.spl:545-638` (`_html_draw_ir_visible`) returns `false` whenever `y0 >= clip.y1` or `y1 <= clip.y0`, using `paint_clip_at(clip_cache, i)`.
  - Measured impact (`chrome_layout_geometry_diff_macos_2026-09-12.md`): at `viewport_h = 760`, only 52 of 1040 Draw IR commands survive (`max_y = 776` vs full `14364`), dropping ~94% of tall documents and even dropping `overflow: hidden` descendants located below `height` because their cached clip was pre-intersected with `default_clip(y1 = height)`.
- **Root Cause:** Draw IR command visibility (`_html_draw_ir_visible_nodes`) uses framebuffer viewport clip (`width x height`) to discard off-viewport document geometry instead of only enforcing explicit CSS `overflow` / scrollport bounds cleanly across the scrollable document height.

### 2.2 Flexbox Row Overlap, Shrinking & Intrinsic Sizing Bugs (`layout_engine.spl`, `layout_text.spl`)
- **Defect F1 — Auto-width nowrap flex items NEVER shrink (`layout_engine.spl:3922 vs 3965`):**
  - Pre-pass (`L3636-3645`) measures `intrinsic_w` for `width_px == 0 and flex_basis_px == 0 and flex_grow == 0`, adds `intrinsic_w` to `sum_explicit`, and adds `flex_shrink * intrinsic_w` to `shrink_scaled_total`.
  - Layout pass (`L3922`) checks `elif shrink_deficit > 0 and shrink_scaled_total > 0 and (cst.width_px != 0 or cst.flex_basis_px > 0):` — explicitly skipping auto-width items! They fall through to `L3965` and take full unshrunk `intrinsic_w`, while `flex_shrink` items shrink by the wrong denominator (`shrink_scaled_total` still counted the auto item) or overlapping right siblings (`space-between`, `margin-left: auto`, right pills/badges).
  - Conversely, when `shrink_deficit > 0` shrinks items to their `min-width: auto` floor (`flex_zero_basis_floor_w` / `min_content`), `L3922` does a single-pass shrink without freezing floored items and redistributing excess deficit to remaining shrinkable siblings (§9.7 freeze loop).
- **Defect F2 — Unclamped & incomplete `row_flex_item_auto_intrinsic_w` (`layout_engine.spl:885-901`, `layout_text.spl:884-885`):**
  - At `L894`, when `intrinsic_text_width > 0` and `inline_margins_w == 0 and pct_pad_w == 0`, `row_flex_item_auto_intrinsic_w` returns `intrinsic` without calling `constrained_outer_width(node, st, ...)` — dropping `min-width`/`max-width`!
  - Also at `L887`, if an auto-width flex item has BOTH inline content and wider block children, `intrinsic_text_width > 0` short-circuits before `flex_item_max_content_width`, underestimating the flex item's width and causing header/card pills or text to overlap adjacent columns!
  - Inside `_lay_flex_item_max_content_width_inner` (`layout_text.spl:884-885`), `cst.width_px > 0` adds `pad_l + pad_r + border_l + border_r` unconditionally even when `cst.border_box` is true, over-sizing `border-box` flex children.
- **Defect F3 — Nowrap `%`-width fallback (`layout_engine.spl:3997-3998`):**
  - `elif cst.width_px < 0: remaining_w = iw` assigns 100% of container width when a negative `%`-sentinel survives non-growing layout, instead of `flex_item_authored_outer_w(nodes[fc], cst, iw)`.
- **Defect F4 — Wrapping row `flex-grow > 0` with `flex-basis: auto` (`layout_engine.spl:3222`, `layout_text.spl:981-988`):**
  - `_lay_flex_wrap_auto_base_width_inner` bails out if `cst.flex_grow != 0`, and `L3222` defaults auto-width/auto-basis items to `iw`. Thus `flex-wrap: wrap` items with `flex-grow: 1; flex-basis: auto` wrap one-per-line at `iw` instead of measuring `max_content`!

### 2.3 Inline & `inline-block` Flow (`layout_engine.spl:4911-5725`)
- **Defect I1 — Float-band empty line flush (`layout_engine.spl:5310`):**
  - `(inline_block or inline_replaced) and inline_x > 0 and inline_x + inline_outer_w > line_iw` checks `inline_x > 0` instead of `inline_x > inline_start_x`. When floats offset `inline_start_x > 0`, an `inline-block` at the start of a line flushes an empty line.
- **Defect I2 — Non-splittable padded/bordered/nowrap `inline` badges (`layout_engine.spl:5139-5201`):**
  - Inline spans with padding/border or `white-space: nowrap` (such as badge/pill `<span style="padding:2px 8px;border:1px solid">`) enter the inline run loop with `inline_w` including padding/border, yet `L5139` (`elif inline_margin_l == 0 and inline_margin_r == 0:`) only tests wrapping on `first_word_advance_width` without the box's horizontal padding/border/margins — and when `white_space_nowrap` is set on an inline span mid-line (`inline_x > inline_start_x`), `L5147` disables line breaking *before* the span (`not cst.white_space_nowrap`)! In Chrome, `white-space: nowrap` prevents wrapping *inside* the span, so if the whole span overflows `line_iw - inline_x`, the line breaks *before* the span!
- **Defect I3 — Inline percentage padding width (`layout_engine.spl:4959`):**
  - Already adds `percent_padding_extra_w` to `inline_w`, and `out_bw[c]` preserves it when unwrapped; however when `cst` is `inline` with padding/border and `white_space_nowrap` breaks before `c`, `inline_x` advances by `out_bw[c] + inline_margin_l + inline_margin_r`.

### 2.4 Block Auto-Height & Float BFC (`layout_engine.spl:5894, 5919, 6130`)
- `float_ctx_establishes_bfc` covers `float_mode != 0`, `position_absolute`/`fixed`, `overflow_hidden`/`auto_y`/`scroll_y`, non-block/inline display (`flow-root`, `inline-block`, `flex`, `grid`, `table-cell`), and `contain: layout`.
- When `layout_with_style_flow` finishes at `L6130`, `cy` expands to `enclosed_float_bottom` ONLY if `float_ctx_count() > g_float_base`. If a child BFC or float pushed floats via `float_ctx_max_bottom_frac`, fractional bottom rounding advances `cy` via `cursor_advance_px(0, enclosed_float_frac)`. Check edge case: when a block has `display: flow-root` with `pad_b == 0` and only a tall float (`float: left`), `h = (cy - y) + pad_b + border_b` properly grows; however if `display: flex` or `display: grid` encloses child floats cleanly, their children ALREADY establish BFC (`parent_display == flex/grid`). Still, verify nested `inline-block` / `flow-root` + `clear` margins so `margin_b` on floats doesn't get dropped when enclosing `cy` (in CSS 2.2 §10.6.7, `float` margin-bottom IS included in `float_ctx` bottom!).

### 2.5 CSS Grid Omitted `grid-template-columns` (`layout_engine.spl:2792-2855`)
- `L2804`: `if st.display == "grid" and (grid_auto_template_n > 0 or grid_explicit_columns.len() > 0 or st.grid_auto_columns != "" or st.grid_auto_flow_column):`
- Any `display: grid` container without `grid-template-columns` (e.g. `display: grid; gap: 10px;` or `grid-template-rows: auto 1fr;` or items with `grid-column: 2`!) silently skips grid layout and executes normal block flow — causing margin collapsing between grid items, ignoring `grid-template-rows`, and breaking `justify-items`/`align-items` and column placement!

### 2.6 Table Auto-Layout Fallback & Row-Group Bounds (`layout_engine.spl:2543-2745`, `layout_foundation.spl:2868-2873`)
- `explicit_auto_table_column_offsets` returns `[]` whenever `not has_authored_spacing and (span != 1 or min_width_px > 0 or max_width_px > 0)` (which hits every `border-collapse: collapse` table with `colspan`, `min-width`, or `max-width`, because `table_spacing_x == 0`).
- Because `layout_engine.spl:2543` requires `auto_column_offsets.len() > 0` when `table_spacing_x == 0 and table_layout != "fixed"`, those tables drop straight into block flow and stack `<td>` elements vertically!
- Additionally, `thead`/`tbody`/`tfoot` row-group widths and heights (`out_bh[table_group]` at `L2739-2743`) only measure `table_y - table_spacing_y - out_by[table_group]`, which omits outer collapse bottom edge `collapse_outer_b` on the closing group and sets nothing if a group has 0 rows.
